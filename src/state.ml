(** State of the program. **)

open Extra
open Sign
open Terms
open Files
open Console

(** Representation of the existing meta-variables. *)
type meta_map =
  { str_map   : meta StrMap.t
  ; int_map   : meta IntMap.t
  ; free_keys : Cofin.t }

(** [empty_meta_map] is an empty meta-variable map. *)
let empty_meta_map : meta_map =
  { str_map   = StrMap.empty
  ; int_map   = IntMap.empty
  ; free_keys = Cofin.full }

(** Representation of the state of the program. *)
type state =
  { loaded : Sign.t PathMap.t
  (** [loaded] stores the signatures of the known (already compiled) modules. An
    important invariant is that all the occurrences of a symbol are physically
    equal (even across different signatures). In particular, this requires the
    objects to be copied when loading an object file. *)

  ; loading : module_path list
  (** [loading] contains the [module_path] of the signatures (or files) that are
    being processed. They are stored in a stack due to dependencies. Note that
    the topmost element corresponds to the current module.  If a [module_path]
    appears twice in the stack, then there is a circular dependency. *)

  ; all_metas : meta_map
  (** [all_metas] is the reference in which the meta-variables are stored. *)

  ; theorem : theorem option }

let initial_state : state =
  { loaded = PathMap.empty
  ; loading = []
  ; all_metas = empty_meta_map
  ; theorem = None }

(** State of the program. *)
let state = ref initial_state

(*****************************************************************************)
(* Signatures. *)

(** [current_sign ()] returns the current signature. *)
let current_sign () =
  let mp =
    match !state.loading with
    | mp :: _ -> mp
    | []      -> assert false
  in
  PathMap.find mp !state.loaded

(** [pp_symbol oc s] prints the name of the symbol [s] to the channel [oc].The
    name is qualified when the symbol is not defined in the current module. *)
let pp_symbol : sym pp = fun oc s ->
  let (path, name) = (s.sym_path, s.sym_name) in
  let sign = current_sign() in
  let full =
    if path = sign.path then name
    else String.concat "." (path @ [name])
  in
  Format.pp_print_string oc full

(** Reset printing function for symbols so that the current module is
    not printed. *)
let _ = Print.pp_symbol_ref := pp_symbol

(** [link sign] establishes physical links to the external symbols. *)
let link : t -> unit = fun sign ->
  let rec link_term t =
    let link_binder b =
      let (x,t) = Bindlib.unbind b in
      Bindlib.unbox (Bindlib.bind_var x (lift (link_term t)))
    in
    match unfold t with
    | Vari(_)     -> t
    | Type        -> t
    | Kind        -> t
    | Symb(s)     -> Symb(link_symb s)
    | Prod(a,b)   -> Prod(link_term a, link_binder b)
    | Abst(a,t)   -> Abst(link_term a, link_binder t)
    | Appl(t,u)   -> Appl(link_term t, link_term u)
    | Meta(_,_)   -> assert false
    | Patt(i,n,m) -> Patt(i, n, Array.map link_term m)
    | TEnv(t,m)   -> TEnv(t, Array.map link_term m)
  and link_rule r =
    let lhs = List.map link_term r.lhs in
    let (xs, rhs) = Bindlib.unmbind r.rhs in
    let rhs = lift (link_term rhs) in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs rhs) in
    {r with lhs ; rhs}
  and link_symb s =
    if s.sym_path = sign.path then s else
    try
      let sign = PathMap.find s.sym_path !state.loaded in
      try find sign s.sym_name with Not_found -> assert false
    with Not_found -> assert false
  in
  let fn _ s =
    s.sym_type  := link_term !(s.sym_type);
    s.sym_def   := Option.map link_term !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.symbols);
  let gn path ls =
    let sign =
      try PathMap.find path !state.loaded
      with Not_found -> assert false in
    let h (n, r) =
      let r = link_rule r in
      let s = find sign n in
      s.sym_rules := !(s.sym_rules) @ [r];
      (n, r)
    in
    Some(List.map h ls)
  in
  sign.deps := filter_map gn !(sign.deps)

(*****************************************************************************)
(* Metavariables. *)

(** [find_meta name] returns the meta-variable mapped to [name] in [all_metas]
    or raises [Not_found] if the name is not mapped. *)
let find_meta : meta_name -> meta = fun name ->
  match name with
  | Defined(s) -> StrMap.find s !state.all_metas.str_map
  | Internal(k) -> IntMap.find k !state.all_metas.int_map

(** [exists_meta name] tells whether [name] is mapped in [all_metas]. *)
let exists_meta : meta_name -> bool = fun name ->
  match name with
  | Defined(s) -> StrMap.mem s !state.all_metas.str_map
  | Internal(k) -> IntMap.mem k !state.all_metas.int_map

(** [add_meta s a n] creates a new user-defined meta-variable named [s], of
    type [a] and arity [n]. *)
let add_meta : string -> term -> int -> meta = fun s a n ->
  let m = { meta_name  = Defined(s)
          ; meta_type  = ref a
          ; meta_arity = n
          ; meta_value = ref None }
  in
  let str_map = StrMap.add s m !state.all_metas.str_map in
  let all_metas = {!state.all_metas with str_map} in
  state := {!state with all_metas};
  m

(** [new_meta a n] creates a new internal meta-variable of type [a] and arity
    [n]. Note that [all_metas] is updated automatically at the same time. *)
let new_meta : term -> int -> meta = fun a n ->
  let (k, free_keys) = Cofin.take_smallest !state.all_metas.free_keys in
  let m = { meta_name  = Internal(k)
          ; meta_type  = ref a
          ; meta_arity = n
          ; meta_value = ref None }
  in
  let int_map = IntMap.add k m !state.all_metas.int_map in
  let all_metas = {!state.all_metas with int_map; free_keys} in
  state := {!state with all_metas};
  m

(** [set_meta m v] sets the value of the metavariable [m] to [v]. *)
let set_meta : meta -> (term, term) Bindlib.mbinder -> unit = fun m v ->
  if !debug_unif then
    begin
      let (xs,v) = Bindlib.unmbind v in
      log "set_meta" "%a[%a] ← %a"
        Print.pp_meta m (Array.pp Print.pp_tvar ",") xs Print.pp v
    end;
  begin
    match m.meta_name with
    | Defined(s)  -> let str_map = StrMap.remove s !state.all_metas.str_map in
                     let all_metas = {!state.all_metas with str_map} in
                     state := {!state with all_metas}
    | Internal(i) -> let int_map = IntMap.remove i !state.all_metas.int_map in
                     let all_metas = {!state.all_metas with int_map} in
                     state := {!state with all_metas}
  end;
  m.meta_type := Kind;
  m.meta_value := Some(v)

(*****************************************************************************)
(* Goals. *)

(** [current_theorem ()] returns the current theorem if we are in a
    proof. It fails otherwise. *)
let current_theorem () : theorem =
  (* We check that we are in a proof. *)
  match !state.theorem with
  | None     -> fatal "not in a proof"
  | Some thm -> thm

(** [fail_if_in_proof()] fails we are in a proof. Does nothing otherwise. *)
let fail_if_in_proof() : unit =
  match !state.theorem with
  | None     -> ()
  | Some _ -> fatal "in a proof"

(** [focus_goal_hyps ()] returns the hypotheses of the currently
    focused goal if we are in a proof, or the empty list otherwise. *)
let focus_goal_hyps () : env =
  match !state.theorem with
  | None     -> []
  | Some thm -> thm.t_focus.g_hyps
