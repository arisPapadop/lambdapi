(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console
open Eval

(** Representation of a set of problems. *)
type problems =
  { type_problems : (Ctxt.t * term * term) list
  (** List of typing problems. *)
  ; sort_problems : term list
  (** List of sorting problems (terms whose types must be sorts). *)
  ; unif_problems : (Ctxt.t * term * term) list
  (** List of unification problems. *)
  ; whnf_problems : (Ctxt.t * term * term) list
  (** List of unification problems that must be put in WHNF first. *)
  ; unsolved      : (Ctxt.t * term * term) list
  (** List of unsolved unification problems. *)
  ; recompute     : bool
  (** Indicates whether unsolved problems should be rechecked. *) }

(** Empty problem. *)
let no_problems : problems =
  { type_problems = [] ; sort_problems = [] ; unif_problems = []
  ; whnf_problems = [] ; unsolved = [] ; recompute = false }

let is_done : problems -> bool = fun p ->
  p.type_problems = [] && p.sort_problems = [] &&
  p.unif_problems = [] && p.whnf_problems = []

(** Representation of solving strategies. *)
type strategy = strategy_aux list
 and strategy_aux =
  | S_Type             (** Deal with typing problems.           *)
  | S_Sort             (** Deal with sorting problems.          *)
  | S_Unif             (** Deal with unification problems.      *)
  | S_Whnf             (** Deal with WHNF unification problems. *)
  | S_Done             (** Check if there is something to do.   *)
  | S_Loop of strategy (** Repeat a strategy indefinitely.      *)

(** [pp_strategy oc s] prints a representation of the strategy [s] to [oc]. *)
let pp_strategy : strategy pp =
  let rec pp_aux oc s =
    match s with
    | S_Type    -> Format.fprintf oc "T"
    | S_Sort    -> Format.fprintf oc "S"
    | S_Unif    -> Format.fprintf oc "U"
    | S_Whnf    -> Format.fprintf oc "W"
    | S_Done    -> Format.fprintf oc "E"
    | S_Loop(l) -> Format.fprintf oc "[%a]" (List.pp pp_aux "") l
  in
  List.pp pp_aux ""

(** Default strategy. *)
let default_strategy : strategy =
  [S_Loop [S_Type; S_Sort; S_Unif; S_Whnf; S_Done]]

(** [eq_vari t u] checks that [t] and [u] are both variables, and the they are
    the same. *)
let eq_vari : term -> term -> bool = fun t u ->
  match (unfold t, unfold u) with
  | (Vari x, Vari y) -> Bindlib.eq_vars x y
  | (_     , _     ) -> false

(** [make_type ()] generates a fresh metavariable of arity [0], and which type
    is [Type]. *)
let make_type =
  let empty = [||] in
  fun () -> Meta(State.new_meta Type 0, empty)

(** [make_meta ctx a] creates a metavariable of type [a],  whth an environment
    containing the variables of context [ctx]. *)
let make_meta : Ctxt.t -> term -> term = fun ctx a ->
  let m = State.new_meta (Ctxt.to_prod ctx a) (List.length ctx) in
  let vs = List.rev_map (fun (v,_) -> Vari v) ctx in
  Meta(m, Array.of_list vs)

(** [make_binder c n d] creates a binder obtained by binding v in the
    term [m[x1,..,xn,v]] of type a sort where [x1,..,xn] are the
    variables of [c] and [v] is a new variable of name [n]. *)
let make_binder : Ctxt.t -> string -> term -> tbinder = fun c n d ->
  let v = Bindlib.new_var mkfree n in
  let u = make_meta ((v,d)::c) (make_type()) in
  Bindlib.unbox (Bindlib.bind_var v (lift u))

(** [make_prod c] creates a term [x:m1[x1,..,xn]->m2[x1,..,xn,x]] of
    type a sort where [x1,..,xn] are the variables of [c] and [x] is a
    new variable of name [no]. *)
let make_prod c =
  let d = make_meta c (make_type()) in d, make_binder c "x" d

(** Representation of unification problems. *)
type unif = Ctxt.t * term * term

let pp_unif : unif pp = fun oc (_,t,u) ->
  Format.fprintf oc "%a = %a" pp t pp u

let pp_unifs : unif list pp = fun oc l ->
  match l with
  | [] -> ()
  | _  -> Format.fprintf oc " if %a" (List.pp pp_unif ", ") l

(** Boolean saying whether user metavariables can be set or not. *)
let can_instantiate : bool ref = ref true

(** [instantiate m ts v] check whether [m] can be instantiated to
    solve the unification problem [m[ts] = v]. Actually make the
    instantiation if it is possible. *)
let instantiate (m:meta) (ts:term array) (v:term) : bool =
  (!can_instantiate || internal m) && distinct_vars ts && not (occurs m v) &&
  let bv = Bindlib.bind_mvar (to_tvars ts) (lift v) in
  Bindlib.is_closed bv && (State.set_meta m (Bindlib.unbox bv); true)

(** Exception raised by the solving algorithm when an irrecuperable
    error is found. *)
let not_convertible t1 t2 =
  fatal "[%a] and [%a] are not convertible" pp t1 pp t2

(** [solve s p] tries to solve the problem [p] following the strategy
    list [s]. When it stops, it returns the list of unsolved
    unification problems. *)
let rec solve : strategy -> problems -> unif list = fun strats p ->
  (*if !debug then log "solve" "%a" pp_strats strats;*)

  (*((typs,sorts,unifs,whnfs,unsolved) as p) : unif list =*)
  match strats with
  | []          -> assert false
  | S_Type    :: l -> solve_types l p
  | S_Sort    :: l -> solve_sorts l p
  | S_Unif    :: l -> solve_unifs l p
  | S_Whnf    :: l -> solve_whnfs l p
  | S_Loop(l) :: _ -> solve (l @ strats) p
  | S_Done    :: l ->
      if is_done p then
        if p.unsolved = [] then []
        else if p.recompute then
          begin
            let problems = {no_problems with unif_problems = p.unsolved} in
            solve (S_Unif::strats) problems
          end
        else p.unsolved
      else solve l p

(** [solve_types s p] tries to solve the typing problems of [p]. Then,
    it continues with the remaining problems following the strategy
    list [s]. *)
and solve_types : strategy -> problems -> unif list = fun strat p ->
  match p.type_problems with
  | []         -> solve strat p
  | (c,t,a)::l -> solve_type c t a strat {p with type_problems = l}

(** [solve_sorts s p] tries to solve the sorting problems of [p]. Then,
    it continues with the remaining problems following the strategy
    list [s]. *)
and solve_sorts : strategy -> problems -> unif list = fun strat p ->
  match p.sort_problems with
  | []   -> solve strat p
  | a::l -> solve_sort a strat {p with sort_problems = l}

(** [solve_unifs s p] tries to solve the unification problems of
    [p]. Then, it continues with the remaining problems following the
    strategy list [s]. *)
and solve_unifs : strategy -> problems -> unif list = fun strat p ->
  match p.unif_problems with
  | []         -> solve strat p
  | (c,t,u)::l -> solve_unif c t u strat {p with unif_problems = l}

(** [solve_whnfs s p] tries to solve the unification problems of [p]
    that msut be weak-head-normalized first. Then, it continues with
    the remaining problems following the strategy list [s]. *)
and solve_whnfs : strategy -> problems -> unif list = fun strat p ->
  match p.whnf_problems with
  | []         -> solve strat p
  | (c,t,u)::l -> solve_whnf c t u strat {p with whnf_problems = l}

(** [solve_type c t a s p] tries to solve the typing problem
    [(c,t,a)]. Then, it continues with the remaining problems
    following the strategy list [s]. *)
and solve_type c t a strats p =
  if !debug_type then log "solve_type" "[%a] [%a]" pp t pp a;
  match unfold t with
  | Patt(_,_,_) | TEnv(_,_) | Kind -> assert false

  | Type ->
      let unif_problems = (c,Kind,a) :: p.unif_problems in
      solve (S_Unif::S_Type::strats) {p with unif_problems}

  | Vari(x) ->
      let typ_x = try Ctxt.find x c with Not_found -> assert false in
      let unif_problems = (c,typ_x,a) :: p.unif_problems in
      solve (S_Unif::S_Type::strats) {p with unif_problems}

  | Symb(s) ->
      let unif_problems = (c,!(s.sym_type),a) :: p.unif_problems in
      solve (S_Unif::S_Type::strats) {p with unif_problems}

  | Prod(t,u_binder) ->
      let c',u = Ctxt.unbind c t u_binder in
      let type_problems = (c,t,Type) :: (c',u,a) :: p.type_problems in
      let sort_problems = a :: p.sort_problems in
      solve (S_Type::S_Sort::strats) {p with type_problems; sort_problems}

  | Abst(t,b_binder) ->
     let u_binder = make_binder c (Bindlib.binder_name b_binder) t in
     let pr = Prod(t,u_binder) in
     let c',b,u = Ctxt.unbind2 c t b_binder u_binder in
     let type_problems = (c,t,Type) :: (c',b,u) :: p.type_problems in
     let unif_problems = (c,pr,a) :: p.unif_problems in
     solve (S_Type::S_Unif::strats) {p with type_problems; unif_problems}

  | Appl(t,u) ->
     let v, w_binder = make_prod c in
     let pr = Prod(v, w_binder) in
     let a' = Bindlib.subst w_binder u in
     let type_problems = (c,t,pr) :: (c,u,v) :: p.type_problems in
     let unif_problems = (c,a',a) :: p.unif_problems in
     solve (S_Type::S_Unif::strats) {p with type_problems; unif_problems}

  | Meta(m, ts) ->
     (* The type of [Meta(m,ts)] is the same as [add_args f ts]
        where [f] is some fresh symbol with the same type as [m]. *)
     let s =
       { sym_name = meta_name m ; sym_type = ref !(m.meta_type)
       ; sym_path = [] ; sym_def  = ref None ; sym_rules = ref []
       ; sym_const = true }
     in
     let t = add_args (Symb s) (Array.to_list ts) in
     solve_type c t a strats p

(** [solve_sort a s p] tries to solve the sorting problem [a]. Then,
    it continues with the remaining problems following the strategy
    list [s]. *)
and solve_sort a strats p : unif list =
  if !debug_type then log "solve_sort" "[%a]" pp a;
  match unfold a with
  | Type | Kind -> solve_sorts strats p
  | _           -> fatal "[%a] is not a sort\n" pp a

(** [solve_unif c t1 t2 s p] tries to solve the unificaton problem
    [(c,t1,t2)]. Then, it continues with the remaining problems
    following the strategy list [s]. *)
and solve_unif c t1 t2 strats p : unif list =
  if t1 == t2 then solve_unifs strats p
  else
    begin
      if !debug_unif then log "solve_unif" "[%a] [%a]" pp t1 pp t2;
      match unfold t1, unfold t2 with
      | Type, Type
      | Kind, Kind -> solve (S_Unif::strats) p

      | Vari x, Vari y when Bindlib.eq_vars x y -> solve (S_Unif::strats) p

      | Prod(a,f), Prod(b,g) | Abst(a,f), Abst(b,g) ->
         let c',u,v = Ctxt.unbind2 c a f g in
         let unif_problems = (c,a,b) :: (c',u,v) :: p.unif_problems in
         solve (S_Unif::strats) {p with unif_problems}

      | Symb(s1), Symb(s2) when s1 == s2 -> solve (S_Unif::strats) p

      | Meta(m1,a1), Meta(m2,a2)
        when m1==m2 && Array.for_all2 eq_vari a1 a2 ->
         solve (S_Unif::strats) p

      | Meta(m,ts), v when instantiate m ts v ->
          solve (S_Unif::strats) {p with recompute = true}
      | v, Meta(m,ts) when instantiate m ts v ->
          solve (S_Unif::strats) {p with recompute = true}

      | Meta(_,_), _
      | _, Meta(_,_) ->
          let whnf_problems = (c,t1,t2) :: p.whnf_problems in
          solve (S_Unif::strats) {p with whnf_problems}

      | Symb(s), _ when not (Sign.is_const s) ->
          let whnf_problems = (c,t1,t2) :: p.whnf_problems in
          solve (S_Unif::strats) {p with whnf_problems}

      | _, Symb(s) when not (Sign.is_const s) ->
          let whnf_problems = (c,t1,t2) :: p.whnf_problems in
          solve (S_Unif::strats) {p with whnf_problems}

      | Appl(_,_), _ | _, Appl(_,_) ->
          let whnf_problems = (c,t1,t2) :: p.whnf_problems in
          solve (S_Unif::strats) {p with whnf_problems}

      | _, _ -> not_convertible t1 t2
    end

(** [solve_whnf c t1 t2 s p] tries to solve the unificaton problem
    [(c,t1,t2)] by first weak-head-normalizing it first. Then, it
    continues with the remaining problems following the strategy list
    [s]. *)
and solve_whnf c t1 t2 strats p : unif list =
  let t1 = whnf t1 and t2 = whnf t2 in
  if !debug_unif then log "solve_whnf" "[%a] [%a]" pp t1 pp t2;
  let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in
  let n1 = List.length ts1 and n2 = List.length ts2 in
  match h1, h2 with
  | Type, Type
  | Kind, Kind -> solve (S_Whnf::strats) p
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)

  | Vari x, Vari y when Bindlib.eq_vars x y && n1 = n2 ->
      let unif_problems =
        let fn l t1 t2 = (c,t1,t2)::l in
        List.fold_left2 fn p.unif_problems ts1 ts2
      in
      solve (S_Whnf::strats) {p with unif_problems}

  | Prod(a,f), Prod(b,g)
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)
  | Abst(a,f), Abst(b,g) ->
  (* We have [ts1=ts2=[]] since [t1] and [t2] are in whnf. *)
     let c',u,v = Ctxt.unbind2 c a f g in
     let unif_problems = (c,a,b) :: (c',u,v) :: p.unif_problems in
     solve (S_Unif::S_Whnf::strats) {p with unif_problems}

  | Symb(s1), Symb(s2) when s1 == s2 && n1 = 0 && n2 = 0 ->
     solve (S_Whnf::strats) p

  | Symb(s1), Symb(s2) when Sign.is_const s1 && Sign.is_const s2 ->
     if s1 == s2 && n1 = n2 then
       let unif_problems =
        let fn l t1 t2 = (c,t1,t2)::l in
        List.fold_left2 fn p.unif_problems ts1 ts2
       in
       solve (S_Unif::S_Whnf::strats) {p with unif_problems}
     else not_convertible t1 t2

  | Meta(m1,a1), Meta(m2,a2)
    when m1 == m2 && n1 = 0 && n2 = 0 && Array.for_all2 eq_vari a1 a2 ->
     solve (S_Whnf::strats) p

  | Meta(m,ts), _ when n1 = 0 && instantiate m ts t2 ->
      solve (S_Whnf::strats) {p with recompute = true}
  | _, Meta(m,ts) when n2 = 0 && instantiate m ts t1 ->
      solve (S_Whnf::strats) {p with recompute = true}

  | Meta(_,_), _
  | _, Meta(_,_) ->
      solve (S_Whnf::strats) {p with unsolved = (c,t1,t2) :: p.unsolved}

  | Symb(s), _ when not (Sign.is_const s) ->
     if eq_modulo t1 t2 then solve (S_Whnf::strats) p
     else solve (S_Whnf::strats) {p with unsolved = (c,t1,t2) :: p.unsolved}

  | _, Symb(s) when not (Sign.is_const s) ->
     if eq_modulo t1 t2 then solve (S_Whnf::strats) p
     else solve (S_Whnf::strats) {p with unsolved = (c,t1,t2) :: p.unsolved}

  | _, _ -> not_convertible t1 t2

(** [solve b strats p] sets [can_instantiate] to [b] and returns
    [Some(l)] if [solve strats p] returns [l], and [None] otherwise. *)
let solve : bool -> strategy -> problems -> unif list option = fun b s p ->
  can_instantiate := b;
  try Some (solve s p) with Fatal(m) -> err "%s\n" m; None

let msg (_,a,b) =
  if !debug_type then err "Cannot solve constraint [%a] ~ [%a]\n" pp a pp b

(** [has_type c t u] returns [true] iff [t] has type [u] in context [c]. *)
let has_type (c:Ctxt.t) (t:term) (a:term) : bool =
  if !debug_type then log "has_type" "[%a] [%a]" pp t pp a;
  let problems = {no_problems with type_problems = [(c,t,a)]} in
  match solve true default_strategy problems with
  | Some l -> List.iter msg l; l = []
  | None   -> false

(** [has_type_with_constrs cs c t u] returns [true] iff [t] has type
    [u] in context [c] and constraints [cs] without instantiating any
    user-defined metavariable. *)
let has_type_with_constr (cs:unif list) (c:Ctxt.t) (t:term) (a:term) : bool =
  if !debug_type then log "has_type_with_constrs" "[%a] [%a]" pp t pp a;
  let problems = {no_problems with type_problems = [(c,t,a)]} in
  match solve false default_strategy problems with
  | Some l ->
     let l = List.filter (fun x -> not (List.mem x cs)) l in
     List.iter msg l; l = []
  | None -> false

(** [infer_constr c t] returns a pair [a,l] where [l] is a list
    of unification problems for [a] to be the type of [t] in context [c]. *)
let infer_constr (c:Ctxt.t) (t:term) : unif list * term =
  if !debug_type then log "infer_constr" "[%a]" pp t;
  let a = make_meta c (make_type()) in
  let problems = {no_problems with type_problems = [(c,t,a)]} in
  match solve true default_strategy problems with
  | Some(l) -> (l, a)
  | None    -> fatal "FIXME1"

(** [infer c t] returns [Some u] if [t] has type [u] in context [c],
    and [None] otherwise. *)
let infer (c:Ctxt.t) (t:term) : term option =
  let l, a = infer_constr c t in
  if l = [] then Some a else (List.iter msg l; None)

(** [sort_type c t] returns [true] iff [t] has type a sort in context [c]. *)
let sort_type (c:Ctxt.t) (t:term) : term =
  if !debug_type then log "sort_type" "[%a]" pp t;
  let a = make_meta c (make_type()) in
  let problems = {no_problems with type_problems = [(c,t,a)]} in
  match solve true default_strategy problems with
  | Some([]) ->
     begin
       match unfold a with
       | Type | Kind -> a
       | _    -> fatal "[%a] has type [%a] (not a sort)" pp t pp a
     end
  | Some(l)  -> List.iter msg l; fatal "FIXME2"
  | None     -> fatal "FIXME3"
