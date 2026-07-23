let pending_routes : string list ref = ref []

let clear () =
  pending_routes := []

let record_coq_label label =
  pending_routes := Camlcoq.camlstring_of_coqstring label :: !pending_routes

let record route =
  pending_routes := route :: !pending_routes

let take () =
  let routes = List.rev !pending_routes in
  pending_routes := [];
  routes

let report routes =
  List.iter
    (fun route -> Printf.eprintf "[tiling-validation] route=%s\n" route)
    routes

let capture f =
  clear ();
  match f () with
  | value -> (value, take ())
  | exception exn ->
      report (take ());
      raise exn

let capture_silent_exception f =
  clear ();
  match f () with
  | value -> (value, take ())
  | exception exn ->
      clear ();
      raise exn
