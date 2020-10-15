(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86
(*
open Int64_overflow
*)

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
   the actual instruction, and the next sevent bytes are InsFrag
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
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x -> 
  match x with
  | Eq ->  (fz = true) 
  | Neq ->  (fz = false) 
  | Lt ->  (fs != fo) 
  | Le ->  (fs != fo || fz=true) 
  | Gt ->  (fs = fo) && (fz = false)
  | Ge ->  (fs = fo) 


(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if addr < mem_bot || addr > mem_top then
    None
  else
    Some (Int64.to_int (Int64.sub addr mem_bot  ))

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

(* for our purposes 0 is sufficiently None *)
let get_mem_ind (addr:int64) : int =  
  let mapped_addr = map_addr addr in
  match mapped_addr with
  | None -> 0
  | Some n -> n

(* resolves an imm to a literal (ignores label, returns 0L) *)
let immception (i:imm) : int64 =
  match i with
  | Lit(li) -> li
  | Lbl(lb) -> 0L

(* Writes a list of 8 sbytes to the memory address addr *)
let rec write_mem (m : mach) (addr : int) (values : sbyte list) : unit =
  match values with
  | [] -> ()
  | h::tl -> m.mem.(addr) <- h; write_mem m (addr+1) tl

(* write_op mach DEST value_to_write *)
let write_op (m : mach) (op : operand) (value : int64) : unit = 
  match op with
  | Imm (t)->  () (* Ignore immediate values, they cannot be a destination*)
  | Reg (reg) -> m.regs.(rind reg) <- value
  | Ind1 (i1) -> () (* Ignore immediate values, they cannot be a destination*)
  | Ind2 (r2) -> let memory_address = m.regs.(rind r2) in (* the effective address *)
    let memory_index = get_mem_ind memory_address in (* the index in the memory  *)
    write_mem m (memory_index) (sbytes_of_int64 value)
  | Ind3 (i3, r3) -> let memory_address = (Int64.add m.regs.(rind r3) (immception i3)) in (* the effective address *)
    let memory_index = get_mem_ind memory_address in (* the index in the memory  *)
    write_mem m (memory_index) (sbytes_of_int64 value)


let read_mem (m:mach) (ind0:int) : int64 =
  let rec rec_read list ind =
    if (ind - ind0) = 8 then
      int64_of_sbytes(list)
    else
      rec_read (list @ [m.mem.(ind)]) (ind+1)
  in 
  rec_read [] ind0


(* read_op mach SRC *)
let read_op (m:mach) (op : operand)  : int64 =
  match op with
  | Imm (t)-> begin match t with
      | Lit(li) -> li
      | Lbl(la) -> 0L
    end
  | Reg (r) -> m.regs.(rind r)
  | Ind1 (r1) -> begin match r1 with
      | Lit(li) -> li
      | Lbl(la) -> 0L
    end
  | Ind2 (r2) -> read_mem m (get_mem_ind m.regs.(rind r2))
  | Ind3 (i3, r3) -> 
    let i = begin match i3 with
      | Lit(li) -> li
      | Lbl(la) -> 0L
    end in
    read_mem m (get_mem_ind (Int64.add m.regs.(rind r3) i))

let get_elem (l:operand list) (ind0:int) : operand =
  let rec rec_get (list: operand list) ind =
    begin match list with 
      | h::tl -> 
        if ind = ind0 then 
          h 
        else 
          (rec_get tl (ind+1))
      | _ -> Imm(Lit(0L))
    end
  in 
  rec_get l 0


let step (m:mach) : unit =
  let inst_byte = m.mem.(get_mem_ind m.regs.( rind Rip)) in
  match inst_byte with
  | InsB0 (opcode, oplist) -> begin match opcode with
      (* movq oplist0 to oplist1 *)
      | Movq -> write_op m (get_elem oplist 1) (read_op m (get_elem oplist 0)) 

      (* pushq SRC: rsp = rsp - 8; move oplist0 to mem(rsp) *)
      | Pushq ->
        write_op m (Reg(Rsp)) (Int64.sub (read_op m (Reg(Rsp))) 8L); 
        write_op m (Ind2(Rsp)) (read_op m (get_elem oplist 0)) 

      (* popq DEST: move mem(rsp) to oplist0; rsp = rsp + 8 *)
      | Popq ->
        write_op m (get_elem oplist 0) (read_op m (Ind2(Rsp))); 
        write_op m (Reg(Rsp)) (Int64.add (read_op m (Reg(Rsp))) 8L)

      (* leaq Ind DEST: store memory address saved in Ind to DEST *)
      | Leaq -> 
        begin match get_elem oplist 0 with
          | Ind1(i) -> write_op m (get_elem oplist 1) (immception i)
          | Ind2(r) -> write_op m (get_elem oplist 1) (read_op m (Reg(r)))
          | Ind3(i,r) ->  write_op m (get_elem oplist 1) (Int64.add (read_op m (Reg(r))) (immception i))
          | _ -> ()
        end
      (* Incq DEST: increment DEST by 1, set flags *)
      | Incq ->
        let open Int64_overflow in
        let result = Int64_overflow.add (read_op m (get_elem oplist 0)) 1L in
        write_op m (get_elem oplist 0) result.value;
        m.flags.fo <- result.overflow;
        m.flags.fs <- result.value < 0L;
        m.flags.fz <- result.value = 0L;
        write_op m (get_elem oplist 0) result.value

      (* Decq DEST: decrement DEST by 1, set flags *)
      | Decq ->
        let open Int64_overflow in
        let result = Int64_overflow.sub (read_op m (get_elem oplist 0)) 1L in
        write_op m (get_elem oplist 0) result.value;
        m.flags.fo <- result.overflow;
        m.flags.fs <- result.value < 0L;
        m.flags.fz <- result.value = 0L;

        (* Negq DEST: negates DEST, sets flags *)
      | Negq ->
        let open Int64_overflow in
        let result = Int64_overflow.neg (read_op m (get_elem oplist 0)) in
        write_op m (get_elem oplist 0) result.value;
        m.flags.fo <- result.overflow;
        m.flags.fs <- result.value < 0L;
        m.flags.fz <- result.value = 0L;

        (* Notq DEST: bitwise not on DEST *)
      | Notq -> 
        write_op m (get_elem oplist 0) (Int64.lognot (read_op m (get_elem oplist 0)))

      (* Addq SRC DEST: dest <- dest + src; sets flags *)
      | Addq ->
        let open Int64_overflow in
        let result = Int64_overflow.add (read_op m (get_elem oplist 1)) (read_op m (get_elem oplist 0)) in
        write_op m (get_elem oplist 1) result.value;
        m.flags.fo <- result.overflow;
        m.flags.fs <- result.value < 0L;
        m.flags.fz <- result.value = 0L;

        (* Subq SRC DEST: dest <- dest - src; sets flags *)
      | Subq ->
        let open Int64_overflow in
        let result = Int64_overflow.sub (read_op m (get_elem oplist 1)) (read_op m (get_elem oplist 0)) in
        write_op m (get_elem oplist 1) result.value;
        m.flags.fo <- result.overflow;
        m.flags.fs <- result.value < 0L;
        m.flags.fz <- result.value = 0L;

        (* Imulq SRC DEST: dest <- dest * src; sets flags *)
      | Imulq ->
        let open Int64_overflow in
        let result = Int64_overflow.mul (read_op m (get_elem oplist 1)) (read_op m (get_elem oplist 0)) in
        write_op m (get_elem oplist 1) result.value;
        m.flags.fo <- result.overflow;
        m.flags.fs <- result.value < 0L;
        m.flags.fz <- result.value = 0L;

        (* Xorq SRC DEST: dest <- dest xor src; sets flags; OF flag always false *)
      | Xorq ->
        let result = Int64.logxor (read_op m (get_elem oplist 1)) (read_op m (get_elem oplist 0)) in 
        write_op m (get_elem oplist 1) result;
        m.flags.fo <- false;
        m.flags.fs <- result < 0L;
        m.flags.fz <- result = 0L;

        (* 
      | Orq
      | Andq
      | Shlq 
      | Sarq 
      | Shrq
      *)

      (* Jmp src1: rip = src1 *)
      | Jmp ->
        write_op m (Reg(Rip)) (read_op m (get_elem oplist 0))

      (* J CC src1: if CC holds then RIP = src1, else RIP -= 8 (at end of step fun it gets incremented) *)
      | J(cnd) ->
        if (interp_cnd m.flags cnd) then 
          write_op m (Reg(Rip)) (read_op m (get_elem oplist 0))
        else
          write_op m (Reg(Rip)) (Int64.sub (read_op m (Reg(Rip))) 8L)

      (* cmpq src1 src2: do src2 - src1; change flags respectively *)
      | Cmpq  ->
        let ret = Int64_overflow.sub (read_op m (get_elem oplist 0)) (read_op m (get_elem oplist 1)) in
          m.flags.fz <- (ret.value = 0L);
          m.flags.fs <- (ret.value < 0L);
          m.flags.fo <- ret.overflow

      (* setb CC Dest: if CC holds then move 1 to DEST's lower byte, else move 0 there *)
      | Set(cnd) ->
        write_op m (get_elem oplist 0) (if (interp_cnd m.flags cnd) then 1L else 0L)

      (* Callq SRC: push rip to top of stack; rsp = rsp - 8; move SRC to rip*)
      | Callq ->
        write_op m (Reg(Rsp)) (Int64.sub (read_op m (Reg(Rsp))) 8L);
        write_op m (Ind2(Rsp)) (read_op m (Reg(Rip)));
        write_op m (Reg(Rip)) (read_op m (get_elem oplist 0)) 

      (* Retq: pop top of stack into rip; rsp = rsp + 8*)
      | Retq -> 
        write_op m (Reg(Rip)) (read_op m (Ind2(Rsp))); 
        write_op m (Reg(Rsp)) (Int64.add (read_op m (Reg(Rsp))) 8L)
      | _ -> ()

      | _ -> ()
    end
  | InsFrag -> () (* never read this you fool *)
  | Byte(b) -> () (* read data byte, this is illegal *)






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
