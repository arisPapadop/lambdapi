(** Commands. *)

open Files
open Terms
open Pos
open Print
open Extra

(** Type of the tests that can be made in a file. *)
type test_type =
  | Convert of term * term (** Convertibility test. *)
  | HasType of term * term (** Type-checking. *)

type test =
  { is_assert : bool (** Should the program fail if the test fails? *)
  ; must_fail : bool (** Is this test supposed to fail? *)
  ; test_type : test_type  (** The test itself. *) }

(** [pp_test oc t] prints the test [t] to channel [oc]. *)
let pp_test : test pp = fun oc test ->
  if test.must_fail then Format.pp_print_string oc "¬(";
  begin
    match test.test_type with
    | Convert(t,u) -> Format.fprintf oc "%a == %a" pp t pp u
    | HasType(t,a) -> Format.fprintf oc "%a :: %a" pp t pp a
  end;
  if test.must_fail then Format.pp_print_string oc ")"

(** Representation of a toplevel command. *)
type cmd = cmd_aux loc
 and cmd_aux =
  (** Symbol declaration (definable when the boolean is [true]). *)
  | SymDecl of bool * strloc * term
  (** Rewriting rules declaration. *)
  | Rules  of (sym * rule) list
  (** Symbol definition (opaque when the boolean is [true]). *)
  | SymDef of bool * strloc * term option * term
  (** Require an external signature. *)
  | Require of module_path
  (** Set debugging flags. *)
  | Debug  of bool * string
  (** Set the verbosity level. *)
  | Verb   of int
  (** Type inference command. *)
  | Infer  of term * Eval.config
  (** Normalisation command. *)
  | Eval   of term * Eval.config
  (** Test command. *)
  | Test   of test
  (** Unimplemented command. *)
  | Other  of strloc
  (** Start proof. *)
  | StartProof of strloc * term
  (** Print focused goal. *)
  | PrintFocus
  (** Refine the focused goal. *)
  | Refine of term
