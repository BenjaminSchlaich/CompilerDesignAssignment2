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
  | None -> raise X86lite_segfault in
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

(*
  returns the address represented by indirection operand on in machine m
*)
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

(*
  step function just for the Sarq operation, because it's condition flags are hell
*)
let stepSarq (m: mach) (o1: operand) (o2: operand): unit =
  let (x, y) = (read_operand m o1, read_operand m o2) in
  let res = (Int64.shift_right y (Int64.to_int x)) in
  let setZeroFlag x = if Int64.equal x 0L then m.flags.fz <- true else m.flags.fz <- false in
  let setSignFlag x = if (Int64.compare x 0L) < 0 then m.flags.fs <- true else m.flags.fs <- false in
    write_operand m res o2;
    (if Int64.equal 0L x then ()
    else ((setSignFlag res; setZeroFlag res);
      (if Int64.equal 1L x then m.flags.fo <- false
      else ())))


(*
  step function just for the Sarq operation, because it's condition flags are hell
*)
let stepShlq (m: mach) (o1: operand) (o2: operand): unit =
  let (x, y) = (read_operand m o1, read_operand m o2) in
  let res = (Int64.shift_left y (Int64.to_int x)) in
  let setZeroFlag x = if Int64.equal x 0L then m.flags.fz <- true else m.flags.fz <- false in
  let setSignFlag x = if (Int64.compare x 0L) < 0 then m.flags.fs <- true else m.flags.fs <- false in
  let topTwoBitsSame = Int64.equal (Int64.logand 1L (Int64.shift_right_logical y 62)) (Int64.shift_right_logical y 63) in
    write_operand m res o2;
    (if Int64.equal 0L x then ()
    else ((setSignFlag res; setZeroFlag res);
      (if Int64.equal 1L x then (
        if topTwoBitsSame then m.flags.fo <- false 
        else m.flags.fo <- true)
      else ())))
let stepShrq (m: mach) (o1: operand) (o2: operand): unit =
  let (x, y) = (read_operand m o1, read_operand m o2) in
  let res = (Int64.shift_right_logical y (Int64.to_int x)) in
  let setZeroFlag x = if Int64.equal x 0L then m.flags.fz <- true else m.flags.fz <- false in
  let setSignFlag x = if Int64.equal x 1L then m.flags.fs <- true else m.flags.fs <- false in
  let msbY = if Int64.equal 1L (Int64.shift_right_logical y 63) then true else false in
    write_operand m res o2;
    (if Int64.equal 0L x then ()
    else (setSignFlag (Int64.shift_right_logical res 63); setZeroFlag res;
      (if Int64.equal 1L x then m.flags.fo <- msbY
      else ())))

let step_binary (m: mach) (oc: opcode) (o1: operand) (o2: operand): unit =
  let read = read_operand m in
  let write = write_operand m in
  let setZeroFlag x = if Int64.equal x 0L then m.flags.fz <- true else m.flags.fz <- false in
  let setSignFlag x = if (Int64.compare x 0L) < 0 then m.flags.fs <- true else m.flags.fs <- false in
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
  | Xorq -> let res = (Int64.logxor (read o1) (read o2)) in (         (* DONE *)
              write res o2;
              setZeroFlag res; setSignFlag res; m.flags.fo <- false)
  | Orq -> let res = (Int64.logor (read o1) (read o2)) in (           (* DONE *)
              write res o2;
              setZeroFlag res; setSignFlag res; m.flags.fo <- false)
  | Andq -> let res = (Int64.logand (read o1) (read o2)) in (         (* DONE *)
              write res o2;
              setZeroFlag res; setSignFlag res; m.flags.fo <- false)
  | Shlq -> stepShlq m o1 o2                                          (* DONE *)
  | Sarq -> stepSarq m o1 o2                                          (* DONE *)
  | Shrq -> stepShrq m o1 o2                                          (* DONE *)
  | Cmpq -> let res = Int64_overflow.sub (read o2) (read o1) in (     (* DONE *)
              m.flags.fo <- res.overflow;
              setSignFlag res.value;
              setZeroFlag res.value)
  | _ -> failwith "unimplemented binary operation"

let rec step_unary (m: mach) (oc: opcode) (on: operand): unit =
  let read = read_operand m in
  let write = write_operand m in
  let setZeroFlag x = if Int64.equal x 0L then m.flags.fz <- true else m.flags.fz <- false in
  let setSignFlag x = if (Int64.compare x 0L) < 0 then m.flags.fs <- true else m.flags.fs <- false in
  let setLowerByte v b = Int64.logor (Int64.logand v 0xFFFFFFFFFFFFFF00L) b in
  match oc with (*Array.set m.regs (rind Rip) (Int64.add 8L m.regs.(rind Rip))*)
  | Pushq -> Array.set m.regs (rind Rsp) (Int64.add m.regs.(rind Rsp) (-8L)); write (read on) (Ind2 Rsp)  (* DONE *)
  | Popq -> write (read (Ind2 Rsp)) on; Array.set m.regs (rind Rsp) (Int64.add m.regs.(rind Rsp) 8L)      (* DONE *)
  | Incq -> step_binary m Addq (Imm (Lit 1L)) on                                                          (* DONE *)
  | Decq -> step_binary m Subq (Imm (Lit 1L)) on                                                          (* DONE *)
  | Negq -> let res = Int64.neg (read on) in                                                              (* DONE *)
            (write res on;
            (if Int64.equal Int64.min_int (read on) then m.flags.fo <- true else (m.flags.fo <- false));
            setZeroFlag res; setSignFlag res)
  | Notq -> write (Int64.lognot (read on)) on                                                             (* DONE *)
  | Jmp -> write (read on) (Reg Rip)
  | J Eq -> if interp_cnd m.flags Eq then step_unary m Jmp on else ()
  | J Neq -> if interp_cnd m.flags Neq then step_unary m Jmp on else ()
  | J Lt -> if interp_cnd m.flags Lt then step_unary m Jmp on else ()
  | J Le -> if interp_cnd m.flags Le then step_unary m Jmp on else ()
  | J Gt -> if interp_cnd m.flags Gt then step_unary m Jmp on else ()
  | J Ge -> if interp_cnd m.flags Ge then step_unary m Jmp on else ()
  | Set Eq -> if interp_cnd m.flags Eq then write (setLowerByte (read on) 1L) on else write (setLowerByte (read on) 0L) on
  | Set Neq -> if interp_cnd m.flags Neq then write (setLowerByte (read on) 1L) on else write (setLowerByte (read on) 0L) on
  | Set Lt -> if interp_cnd m.flags Lt then write (setLowerByte (read on) 1L) on else write (setLowerByte (read on) 0L) on
  | Set Le -> if interp_cnd m.flags Le then write (setLowerByte (read on) 1L) on else write (setLowerByte (read on) 0L) on
  | Set Gt -> if interp_cnd m.flags Gt then write (setLowerByte (read on) 1L) on else write (setLowerByte (read on) 0L) on
  | Set Ge -> if interp_cnd m.flags Ge then write (setLowerByte (read on) 1L) on else write (setLowerByte (read on) 0L) on
  | Callq -> (step_unary m Pushq (Reg Rip); step_binary m Movq on (Reg Rip))
  | _ -> failwith "unimplemented unary operation"

let step_noarg (m:mach) (oc: opcode): unit =
  match oc with
  | Retq -> step_unary m Popq (Reg Rip)
  | _ -> failwith "unimplemented noarg operation"

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

type celem = { lbl: lbl; global: bool; inst: ins list; size: int64 }
type delem = { lbl: lbl; global: bool; data: data list; size: int64 }

(* sort the program into instructions and data*)
let separate (p: prog): (celem list * delem list) =
  let cslen cs = Int64.mul 8L @@ Int64.of_int (List.length cs) in
  let dlen d = 
    match d with
    | Asciz s -> Int64.of_int @@ String.length s + 1
    | Quad _ -> 8L in
  let dslen ds = List.fold_left (fun s b -> Int64.add s @@ dlen b) 0L ds in
  let sort (c, d) (e: elem) =
    match e.asm with
    | Text [] -> (c, d)             (* empty code block is dropped immediately *)
    | Data [] -> (c, d)             (* empty data block is dropped, too *)
    | Text cs -> ({lbl = e.lbl; global = e.global; inst = cs; size = cslen cs} :: c, d)
    | Data ds -> (c, {lbl = e.lbl; global = e.global; data = ds; size = dslen ds} :: d)
  in
  List.fold_left sort ([], []) p

let testSegLength (p: celem list): int64 =
  List.fold_left (fun s (e: celem) -> Int64.add s e.size) 0L p

let dataSegLength (p: delem list): int64 =
  List.fold_left (fun s (e: delem) -> Int64.add s e.size) 0L p

type symTable = {mutable entries: (lbl * quad) list; mutable head: quad}

let rec lookup (ls: (lbl*quad) list) (lab: lbl): quad option =
  match ls with
  | [] -> None
  | (l, q)::xs -> if l = lab then Some q else lookup xs lab

let buildTableI (p: celem list) (start: quad): symTable =
  let t = {entries = []; head = start} in
  let locup = lookup t.entries in
  let insert (ce: celem): unit = 
    match locup ce.lbl with
    | Some _ -> raise @@ Redefined_sym ce.lbl
    | None -> t.entries <- (ce.lbl, t.head) :: t.entries; t.head <- Int64.add t.head ce.size
  in
  List.iter insert p; t

let buildTableD (p: delem list) (start: quad): symTable =
  let t = {entries = []; head = start} in
  let locup = lookup t.entries in
  let insert (ce: delem): unit = 
    match locup ce.lbl with
    | Some _ -> raise @@ Redefined_sym ce.lbl
    | None -> t.entries <- (ce.lbl, t.head) :: t.entries; t.head <- Int64.add t.head ce.size
  in
  List.iter insert p; t

(*  replace occurences of a lable in i with the address for that label in the symTable t.
    if a label is not found, a Undefined_symbol exception is raised.
*)
let patchInstruction (t: symTable) (i: ins): ins =
let locup = lookup t.entries in
let patchOperand (on: operand): operand =
  match on with
  | Imm (Lbl l) -> (match locup l with
                    | Some q -> Imm (Lit q)
                    | None -> raise @@ Undefined_sym l)
  | Ind1 (Lbl l) -> (match locup l with
                    | Some q -> Ind1 (Lit q)
                    | None -> raise @@ Undefined_sym l)
  | Ind3 (Lbl l, r) -> (match locup l with
                      | Some q -> Ind3 (Lit q, r)
                      | None -> raise @@ Undefined_sym l)
  | _ -> on
in
let (oc, ol) = i in
(oc, List.map patchOperand ol)

let patchData (t: symTable) (d: data): data =
  let locup = lookup t.entries in
  match d with
  | Quad (Lbl l) -> (match locup l with
                    | Some q -> Quad (Lit q)
                    | None -> raise @@ Undefined_sym l)
  | _ -> d
  

let assemble (p:prog) : exec =
  let (textSeg, dataSeg) = separate p in
  let iTable = buildTableI textSeg mem_bot in
  let dTable = buildTableD dataSeg iTable.head in
  let sTable = {entries = iTable.entries @ dTable.entries; head = dTable.head} in
  let patchedText =
    List.map (function | (ce: celem) -> {lbl = ce.lbl; global = ce.global; inst = List.map (patchInstruction sTable) ce.inst; size = ce.size}) textSeg
  in
  let patchedData =
    List.map (function | (de: delem) -> {lbl = de.lbl; global = de.global; data = List.map (patchData sTable) de.data; size = de.size}) dataSeg
  in
  {
    entry = (match lookup iTable.entries "main" with | Some q -> q | None -> raise @@ Undefined_sym "main");
    text_pos = mem_bot;
    data_pos = iTable.head;
    text_seg = List.concat_map sbytes_of_ins (List.concat_map (function ce -> ce.inst) patchedText);
    data_seg = List.concat_map sbytes_of_data (List.concat_map (function de -> de.data) patchedData)
  }

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
