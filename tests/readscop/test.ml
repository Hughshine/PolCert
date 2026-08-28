open Printf 
open OpenScopReader
open OpenScopPrinter

let failed = ref false
let attempted = ref 0
let passed = ref 0

let report_failure message =
  failed := true;
  eprintf "[legacy/readscop] FAIL expected=parse-success actual=parse-failure interpretation=%s\n" message

let loop filename = 
  attempted := !attempted + 1;
  let outfilename = filename ^ ".output" in
  (match read_and_print filename outfilename with
   | Some p ->
      passed := !passed + 1;
      printf "[legacy/readscop] PASS case=%s expected=parse-success actual=parse-success interpretation=OpenScop-input-was-read-and-reprinted\n" filename
   | None -> report_failure (sprintf "Parsing openscop file %s." filename))

(** test both printer and reader *)
let () = 
  for i = 1 to Array.length Sys.argv - 1 do
    loop Sys.argv.(i); 
    loop (Sys.argv.(i) ^ ".output")
  done;
  if !failed then exit 1
  else printf "[legacy/readscop] PASS expected=%d actual=%d interpretation=all-OpenScop-roundtrip-parses-succeeded\n" !attempted !passed
;;
