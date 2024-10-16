open Assert
open X86
open Simulator
open Asm

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)

let testTableBlocks: celem list = [ {lbl = "main"; global = true; inst = [Retq,[]]; size = 8L};
                                    {lbl = "main"; global = true; inst = [Retq,[]]; size = 8L}]

let undefinedsym_test (p: celem list) () =
  try ignore (buildTableI p 0L);
    failwith "Should have raised Undefined_sym"
  with 
    | Undefined_sym _ -> ()
    | _ -> failwith "Should have raised Undefined_sym"

let provided_tests : suite = [(*
  Test ("Debug buildTableI", [
    "raise Redefined_sym", undefinedsym_test testTableBlocks
  ]);*)

] 
