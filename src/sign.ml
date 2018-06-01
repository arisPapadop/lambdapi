(** Signature for symbols. *)

open Console
open Files
open Terms
open Pos
open Extra

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { symbols : sym StrMap.t ref
  ; path    : module_path
  ; deps    : (string * rule) list PathMap.t ref }

(* NOTE the [deps] field contains a hashtable binding the [module_path] of the
   external modules on which the current signature depends to an association
   list. This association list then maps definable symbols of the external
   module to additional reduction rules defined in the current signature. *)

(** [create path] creates an empty signature with module path [path]. *)
let create : module_path -> t = fun path ->
  { path ; symbols = ref StrMap.empty ; deps = ref PathMap.empty }

(** [find sign name] finds the symbol named [name] in [sign] if it exists, and
    raises the [Not_found] exception otherwise. *)
let find : t -> string -> sym =
  fun sign name -> StrMap.find name !(sign.symbols)

(** [mem sign name] checks whether the symbol named [name] exists in [sign]. *)
let mem : t -> string -> bool =
  fun sign name -> StrMap.mem name !(sign.symbols)

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of our
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s = s.sym_type := Kind; s.sym_rules := [] in
  let rec unlink_term t =
    let unlink_binder b = unlink_term (snd (Bindlib.unbind b)) in
    let unlink_term_env t =
      match t with
      | TE_Vari(_) -> ()
      | _          -> assert false (* Should not happen, matching-specific. *)
    in
    match unfold t with
    | Vari(_)      -> ()
    | Type         -> ()
    | Kind         -> ()
    | Symb(s)      -> if s.sym_path <> sign.path then unlink_sym s
    | Prod(a,b)    -> unlink_term a; unlink_binder b
    | Abst(a,t)    -> unlink_term a; unlink_binder t
    | Appl(t,u)    -> unlink_term t; unlink_term u
    | Meta(_,_)    -> assert false (* Should not happen, uninstantiated. *)
    | Patt(_,_,_)  -> () (* The environment only contains variables. *)
    | TEnv(t,m)    -> unlink_term_env t; Array.iter unlink_term m
  and unlink_rule r =
    List.iter unlink_term r.lhs;
    let (_, rhs) = Bindlib.unmbind r.rhs in
    unlink_term rhs
  in
  let fn _ s =
    unlink_term !(s.sym_type);
    Option.iter unlink_term !(s.sym_def);
    List.iter unlink_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.symbols);
  let gn _ ls = List.iter (fun (_, r) -> unlink_rule r) ls in
  PathMap.iter gn !(sign.deps)

(** [new_symbol sign definable name a] creates a new [definable]
    symbol named [name] of type [a] in the signature [sign]. The
    created symbol is also returned. WARNING: [name] must NOT be
    already defined. *)
let new_symbol : t -> bool -> strloc -> term -> sym =
  fun sign definable s sym_type ->
  let { elt = sym_name } = s in
  (*if StrMap.mem sym_name !(sign.symbols) then
    fatal "%S is already defined." sym_name;*)
  let sym =
    { sym_name = sym_name ; sym_type = ref sym_type ; sym_path = sign.path
    ; sym_def  = ref None ; sym_rules = ref [] ; sym_const = not definable }
  in
  sign.symbols := StrMap.add sym_name sym !(sign.symbols);
  out 3 "[symb] %s\n" sym_name; sym

(** [is_const s] tells whether the symbol is constant. *)
let is_const : sym -> bool = fun s ->
  s.sym_const || (!(s.sym_rules) = [] && !(s.sym_def) = None)

(** [write sign file] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit = fun sign fname ->
  match Unix.fork () with
  | 0 -> let oc = open_out fname in
         unlink sign; Marshal.to_channel oc sign [Marshal.Closures];
         close_out oc; exit 0
  | i -> ignore (Unix.waitpid [] i)

(* NOTE [Unix.fork] is used to safely [unlink] and write an object file, while
   preserving a valid copy of the written signature in the parent process. *)

(** [read fname] reads a signature from the object file [fname]. Note that the
    file can only be read properly if it was build with the same binary as the
    one being evaluated. If this is not the case, the program gracefully fails
    with an error message. *)
let read : string -> t = fun fname ->
  let ic = open_in fname in
  try
    let sign = Marshal.from_channel ic in
    close_in ic; sign
  with Failure _ ->
    close_in ic;
    fatal "File [%s] is incompatible with the current binary...\n" fname

(* NOTE here, we rely on the fact that a marshaled closure can only be read by
   processes running the same binary as the one that produced it. *)

(** [add_rule def r] adds the new rule [r] to the definable symbol [def]. When
    the rule does not correspond to a symbol of the current signature,  it  is
    also stored in the dependencies. *)
let add_rule : t -> sym -> rule -> unit = fun sign sym r ->
  sym.sym_rules := !(sym.sym_rules) @ [r];
  out 3 "[rule] %a\n" Print.pp_rule (sym, r);
  if sym.sym_path <> sign.path then
    let m =
      try PathMap.find sym.sym_path !(sign.deps)
      with Not_found -> assert false
    in
    sign.deps := PathMap.add sym.sym_path ((sym.sym_name,r) :: m) !(sign.deps)
