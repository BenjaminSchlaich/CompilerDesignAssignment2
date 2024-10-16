open Assert
open X86
open Simulator

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)

let printInt64Opt (io: int64 option): string =
  match io with
  | None -> "None"
  | Some i -> Int64.to_string i

let provided_tests : suite = [
  Test ("Debug Lookup", [
    (let res = (lookup [("l1", 1L); ("l2", 2L); ("main", 5L)] "main") in
    ("lookup exists", assert_eq (Some 4L) res));
    (let res = (lookup [("l1", 1L); ("l2", 2L)] "main") in
    ("lookup expected None and got " ^ printInt64Opt res, assert_eq None res))
  ]);

] 
