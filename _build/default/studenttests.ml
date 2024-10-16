open Assert
open X86
open Simulator

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)

let printInt64Opt (io: int64 option): string =
  match io with
  | None -> "None"
  | Some i -> Int64.to_string i

let printSbyte (sb: sbyte): string =
  match sb with
  | (InsB0 i) -> string_of_ins i
  | _ -> "DATA"

let printSbyteList: (sbyte list -> string) =
  List.fold_left (fun s b -> s ^ printSbyte b) ""

let helloworld = [ text "foo"
                  [ Xorq, [~%Rax; ~%Rax]
                  ; Movq, [~$100; ~%Rax]
                  ; Retq, []
                  ]
                  ; text "main" 
                  [ Xorq, [~%Rax; ~%Rax]
                  ; Movq, [Ind1 (Lbl "baz"); ~%Rax]
                  ; Retq, []
                  ]
                  ; data "baz" 
                  [ Quad (Lit 99L)
                  ; Asciz "Hello, world!"
                  ]
]

let provided_tests : suite = [
  Test ("Debug Lookup", [
    (let res = (lookup [("l1", 1L); ("l2", 2L); ("main", 5L)] "main") in
    ("lookup exists", assert_eq (Some 4L) res));
    (let res = (lookup [("l1", 1L); ("l2", 2L)] "main") in
    ("lookup expected None and got " ^ printInt64Opt res, assert_eq None res))
  ]);

  Test ("Debug Assemble1", [
    (let res = (lookup [("l1", 1L); ("l2", 2L); ("main", 5L)] "main") in
    ("lookup exists", assert_eq (Some 4L) res));
  ]);
] 
