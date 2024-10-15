(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = function
  | Eq -> fz
  | Neq -> not fz
  | Gt -> not ((fs <> fo) || fz)
  | Ge -> fs = fo
  | Lt -> fs <> fo
  | Le -> (fs <> fo) || fz

(* Eq | Neq | Gt | Ge | Lt | Le *)

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if addr < mem_bot || addr >= mem_top then None
  else Some (Int64.to_int (Int64.sub addr mem_bot))

(*
  Step 1 in step function:
    given an architecture, returns the next instruction to be executed
*)
let fetch (m: mach): ins =
  let instrAddr = m.regs.(rind Rip) in
  let instrBytes = match map_addr instrAddr with
  | Some q -> m.mem.(q)
  | None -> failwith "trying to fetch from invalid address." in
  match instrBytes with
  | (InsB0 i) -> i
  | _ -> failwith "trying to fetch non-instruction quadword."

(*
  generic helper for step function
  Get a value out of a Some, with a very bad exception mechanism. -> Only use when you're sure that None won't be returned.
*)
let trySome = function
| (Some x) -> x
| None -> raise X86lite_segfault

(*
  generic helper for step function
  Given a address (quad), loads the quad in the memory of m at that address
*)
let load_quad (m: mach) (addr: quad): quad =
  let open List in
  let (base: int) = trySome (map_addr addr) in
    int64_of_sbytes (map (function (offset: int) -> m.mem.(base + offset)) [0;1;2;3;4;5;6;7])

let get_addr (m: mach) (o: operand): quad =
  match o with
  | Ind1 (Lit l) -> l
  | Ind2 r -> m.regs.(rind r)
  | Ind3 ((Lit l), r) -> Int64.add l m.regs.(rind r)
  | _ -> failwith "call to getAddr from non-memory operand or unresolved label."

(*
  Step 2 in step function:
    Retrieve the value for the operand o in machine m.
*)
let read_operand (m: mach) (o: operand): quad =
  match o with
  | Imm (Lit l) -> l
  | Reg r -> m.regs.(rind r)
  | _ -> load_quad m (get_addr m o)

(*
  Helper for write_operand: store the value v to address a in machine m.
*)
let store_quad (m: mach) (v: quad) (a: quad): unit = 
  let base = trySome (map_addr a) in
  let fill = List.combine [0;1;2;3;4;5;6;7] (sbytes_of_int64 v) in
    List.iter (function (index, sb) -> Array.set m.mem (base + index) sb) fill

(*
  Step 4 in the step function:
  Save the value v of some computation to the operand o in machine m.
*)
let write_operand (m: mach) (v: quad) (d: operand) =
  match d with
  | Reg r -> Array.set m.regs (rind r) v
  | _ -> store_quad m v (get_addr m d)

let step_noarg (m:mach) (oc: opcode): unit =
  let read = read_operand m in
  let write = write_operand m in
  match oc with
  | _ -> failwith "unimplemented unary operation"

let step_unary (m: mach) (oc: opcode) (on: operand): unit =
  let read = read_operand m in
  let write = write_operand m in
  match oc with (*Array.set m.regs (rind Rip) (Int64.add 8L m.regs.(rind Rip))*)
  | Pushq -> Array.set m.regs (rind Rsp) (Int64.add m.regs.(rind Rsp) (-8L)); write (read on) (Ind2 Rsp)
  | Popq -> write (read (Ind2 Rsp)) on; Array.set m.regs (rind Rsp) (Int64.add m.regs.(rind Rsp) 8L)
  | Incq -> write (Int64.succ (read on)) on
  | Decq -> write (Int64.pred (read on)) on
  | Negq -> write (Int64.neg (read on)) on
  | Notq -> write (Int64.lognot (read on)) on
  | Jmp -> write (read on) (Reg Rip)
  | _ -> failwith "unimplemented unary operation"

let step_binary (m: mach) (oc: opcode) (o1: operand) (o2: operand): unit =
  let read = read_operand m in
  let write = write_operand m in
  let setSignFlag x = if Int64.equal x 0L then m.flags.fz <- true else m.flags.fz <- false in
  let setZeroFlag x = if (Int64.compare x 0L) < 0 then m.flags.fs <- true else m.flags.fs <- false in
  let arithm (f: (int64 -> int64 -> Int64_overflow.t)): unit = (
    let res = f (read o2) (read o1) in
      write res.value o2;
      m.flags.fo <- res.overflow;
      setSignFlag res.value;
      setZeroFlag res.value) in
  match oc with
  | Movq -> write (read o1) o2                  (* DONE *)
  | Leaq -> write (get_addr m o1) o2            (* DONE *)
  | Addq -> arithm Int64_overflow.add           (* DONE *)
  | Subq -> arithm Int64_overflow.sub           (* DONE *)
  | Imulq -> arithm Int64_overflow.mul          (* DONE *)
  | Xorq -> let res = (Int64.logxor (read o1) (read o2)) in (
              write res o2;
              setZeroFlag res; setSignFlag res; m.flags.fo <- false)
  | Orq -> let res = (Int64.logor (read o1) (read o2)) in (
              write res o2;
              setZeroFlag res; setSignFlag res; m.flags.fo <- false)
  | Andq -> let res = (Int64.logand (read o1) (read o2)) in (
              write res o2;
              setZeroFlag res; setSignFlag res; m.flags.fo <- false)
  | Shlq -> write (Int64.shift_left (read o2) (Int64.to_int (read o1))) o2
  | Sarq -> write (Int64.shift_right (read o2) (Int64.to_int (read o1))) o2
  | Shrq -> write (Int64.shift_right (read o2) (Int64.to_int (read o1))) o2(*TODO*)
  | Cmpq -> let rslt = Int64.sub (read o2) (read o1) in
    ()
  | _ -> failwith "unimplemented binary operation"

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  let (oc, ol) = fetch m in
  let open List in
  let (noarg, binary) = (
    [Retq],
    [Movq; Leaq; Addq; Subq; Imulq; Xorq; Orq; Andq; Shlq; Sarq; Shrq; Cmpq]
  ) in (
  (Array.set m.regs (rind Rip) (Int64.add 8L m.regs.(rind Rip)));
  if mem oc noarg then step_noarg m oc
  else if mem oc binary then step_binary m oc (hd ol) (hd (tl ol))
  else step_unary m oc (hd ol)
  )

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =
failwith "assemble unimplemented"

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
failwith "load unimplemented"
