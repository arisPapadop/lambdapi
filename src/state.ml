type t = { mutable next : t option ; undo : unit -> unit }

let current : t ref = ref { next = None ; undo = (fun () -> ()) }

let save : unit -> t = fun () -> !current

let rollback : t -> unit = fun t ->
  let rec fn = function
    | None   -> ()
    | Some t -> t.undo (); let n = t.next in t.next <- None; fn n
  in fn t.next; t.next <- None; current := t

let set : 'a ref -> 'a -> unit = fun r v ->
  let v0 = !r in
  let t = { next = None; undo = (fun () -> r := v0) } in
  !current.next <- Some t; current := t; r := v
