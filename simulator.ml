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
let debug_simulator = ref true

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
  begin match inst_byte with
    | InsB0 (opcode, oplist) -> (begin match opcode with
        (* movq oplist0 to oplist1 *)
        | Movq -> write_op m (get_elem oplist 1) (read_op m (get_elem oplist 0));
          (* 
          if !debug_simulator then print_endline @@ Int64.to_string(read_op m (get_elem oplist 0));
          if !debug_simulator then print_endline @@ string_of_ins (opcode, oplist);
          if !debug_simulator then print_endline @@ Int64.to_string(read_op m (get_elem oplist 1));
          *)


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

          (* Orq SRC DEST: dest <- dest or src; sets flags; OF flag always false *)

        | Orq ->
          let result = Int64.logor (read_op m (get_elem oplist 1)) (read_op m (get_elem oplist 0)) in 
          write_op m (get_elem oplist 1) result;
          m.flags.fo <- false;
          m.flags.fs <- result < 0L;
          m.flags.fz <- result = 0L;

          (* Andq SRC DEST: dest <- dest and src; sets flags; OF flag always false *)
        | Andq ->
          let result = Int64.logand (read_op m (get_elem oplist 1)) (read_op m (get_elem oplist 0)) in 
          write_op m (get_elem oplist 1) result;
          m.flags.fo <- false;
          m.flags.fs <- result < 0L;
          m.flags.fz <- result = 0L;


          (* Sarq AMT DEST dest <- dest >> amt; set flags if amt !=0; OF flag is true if amt == 1*)
        | Sarq -> 
          let amt = read_op m (get_elem oplist 0) in
          let old_dest = read_op m (get_elem oplist 1) in
          let result = Int64.shift_right old_dest (Int64.to_int amt) in 
          if amt != 0L then (
            m.flags.fs <- result < 0L;
            m.flags.fz <- result = 0L;
            if amt = 1L then
              m.flags.fo <- false;
          );
          write_op m (get_elem oplist 1) result;


          (* Shrq AMT DEST: dest <- dest >> amt; set flags if amt !=0; OF flag is MSB of old dest if amt == 1 *)
        | Shrq -> 
          let amt = read_op m (get_elem oplist 0) in
          let old_dest = read_op m (get_elem oplist 1) in
          let result = Int64.shift_right_logical old_dest (Int64.to_int amt) in 
          if amt != 0L then (
            m.flags.fs <- result < 0L;
            m.flags.fz <- result = 0L;
            if amt = 1L then
              m.flags.fo <- (Int64.shift_right_logical old_dest 63) = 1L;
          );
          write_op m (get_elem oplist 1) result;


          (*Shlq AMT DEST: shift dest left by amt, read flag magic in docu *)
        | Shlq ->
          let amt = (Int64.to_int (read_op m (get_elem oplist 0))) in
          let res = Int64.shift_left (read_op m (get_elem oplist 1)) amt in
          let orig_dest_op = (get_elem oplist 1) in
          write_op m orig_dest_op res;
          if amt != 0 then
            m.flags.fs <- res < 0L;
          m.flags.fz <- res = 0L;
          if amt = 1 then
            let orig_dest_val = (read_op m orig_dest_op)in
            m.flags.fo <- Int64.logand (Int64.shift_right_logical orig_dest_val 62) 1L = Int64.logand (Int64.shift_right_logical orig_dest_val 63) 1L;

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
          let open Int64_overflow in
          let ret = Int64_overflow.sub (read_op m (get_elem oplist 1)) (read_op m (get_elem oplist 0)) in
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

      end);
      write_op m (Reg(Rip)) (Int64.add (read_op m (Reg(Rip))) 8L);

    | InsFrag -> () (* never read this you fool *)
    | Byte(b) -> () (* read data byte, this is illegal *)
  end


(* Increment instruction pointer *)




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


(* extracts all elems containing text into text_only_list and all elems containing data into data_only_list  *)
let rec split_text_data (remaining_list: elem list) ((text_only_list, data_only_list) : (elem list * elem list)) : (elem list * elem list) = 
  match remaining_list with
  | [] ->  (text_only_list, data_only_list)
  | h::tl -> begin match h.asm with 
      | Text(ins) -> split_text_data tl (text_only_list@[h], data_only_list)
      | Data(data) -> split_text_data tl (text_only_list, data_only_list@[h])
    end 

(* Convert an X86 program into an object file:
   + separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

   HINT: List.fold_left and List.fold_right are your friends.
*)

type sym = (string * int64 * int64)

(* calculates data size:
- for strings: string.length + 1, because strings terminate with 0
- for quads 8 bytes
*)
let calc_data_size (cur_size: int64) (cur_data: data) : int64 =
  match cur_data with
  | Asciz(str) -> Int64.add cur_size (Int64.of_int ((String.length str)+1))
  | Quad(q) -> Int64.add cur_size 8L

(* calculates element size:
- for text 8 bytes per element in list "insts"
- for data use calc_data size to add up all sizes of data
*)
let calc_elem_size (cur_elem: elem) : int64 = 
  match cur_elem.asm with
  | Text(insts)-> Int64.mul 8L (Int64.of_int (List.length insts))
  | Data(datas) -> List.fold_left calc_data_size 0L datas

(* 
adds element to sym list, for entry in sym_list:
- lbl = lbl of elem
- adress = (adress of previous entry) + (size of previous entry) 
(- if first item in list, adress = mem_bot = 0x400000L)
- site = elem size (use function calc_elem_size)
*)
let create_sym_entry (incomplete_list :sym list) (cur_elem: elem) : (sym list) = 
  match incomplete_list with
  | [] -> [(cur_elem.lbl, mem_bot, calc_elem_size cur_elem)]
  | h::tl -> let (_,last_mem_addr,last_sym_size) = h in 
    let cur_size = calc_elem_size cur_elem in
    [(cur_elem.lbl, Int64.add last_mem_addr last_sym_size , cur_size )]@incomplete_list

(* 
returns adress of top element of sym list:
- if list not empty: adress = (adress of previous elem) + (size of previous elem)
- if list empty:  mem_bot = 0x400000L
*)
let calc_data_bottom_addr (text_sym_tbl: sym list) : int64 =
  match text_sym_tbl with
  | [] -> mem_bot
  | h::tl -> let ( _, data_bottom_addr ,size_of_last_symbol) = h in Int64.add data_bottom_addr size_of_last_symbol

(* converts data list element-wise to sbyte list*)
let rec sbytes_of_data_list (datas: data list) : sbyte list =
  match datas with
  | [] -> []
  | h::tl -> (sbytes_of_data h)@(sbytes_of_data_list tl)

(* search for a label in sym_table, if found return adress, else raise exception *)
let lbl_to_lit (wanted_lbl: string) (init_sym_table : sym list) : int64 =
  let rec rec_lbl_to_lit sym_table = 
    match sym_table with
    | [] -> raise (Undefined_sym wanted_lbl)
    | h::tl -> let (lbl,addr,_) = h in
      if lbl = wanted_lbl then 
        addr
      else 
        rec_lbl_to_lit tl
  in 
  rec_lbl_to_lit init_sym_table

(* if there is a label in ins, replace it with address from sym list *)
let replace_lbl (cur_ins: ins) (sym_tbl: sym list) : ins = 

  let rec replace_lbl_from_operand_list (op_list: operand list) : operand list = 
    let replace_lbl_from_operand (op: operand) : operand =  
      match op with
      | Imm(Lit(imm)) -> Imm(Lit(imm))
      | Imm(Lbl(lbl)) -> Imm(Lit(lbl_to_lit lbl sym_tbl))
      | Reg(r) -> Reg(r)
      | Ind1(Lit(imm)) -> Imm(Lit(imm))
      | Ind1(Lbl(lbl)) -> Imm(Lit(lbl_to_lit lbl sym_tbl))
      | Ind2(r) -> Ind2(r)
      | Ind3(Lit(imm), r) -> Ind3(Lit(imm), r)
      | Ind3(Lbl(lbl), r) -> Ind3(Lit(lbl_to_lit lbl sym_tbl), r)
    in

    match op_list with
    | [] -> []
    | h::tl -> [replace_lbl_from_operand h]@(replace_lbl_from_operand_list tl)
  in

  let (opcode, operands) = cur_ins in
  (opcode, replace_lbl_from_operand_list operands) 

(*
converts elem list of type ins to sbyte list. 
- calls element-wise "sbytes_of_ins", if theres is 
- checks every inst-elem if theres is a label
 *)
let sbytes_of_ins_list (init_inst_list: ins list) (sym_tbl: sym list) : sbyte list =
  let rec rec_sbytes_of_ins_list insts =
    match insts with
    | [] -> []
    | h::tl -> (sbytes_of_ins (replace_lbl h sym_tbl))@(rec_sbytes_of_ins_list tl)

  in
  rec_sbytes_of_ins_list init_inst_list

(*
creates an sbyte from an elem. 
if text, we need to take care of labels in text
if data, convert to sbytes with "sybtes_of_data_list" 
 *)
let create_sbyte_from_elem (cur_elem: elem) (sym_tbl: sym list) : sbyte list = 
  match cur_elem.asm with 
  | Text(insts) -> sbytes_of_ins_list insts sym_tbl
  | Data(datas) -> sbytes_of_data_list datas

(*
creates an sbyte list from  elem list. 
- elem list is text only or data only
- call element-wise fun "create_sbyte_from_elem"
 *)
let rec create_seg (element_list: elem list) (sym_tbl: sym list) : sbyte list =
  match element_list with
  | [] -> []
  | h::tl -> let sbytes_of_head = create_sbyte_from_elem h sym_tbl in 
    sbytes_of_head@(create_seg tl sym_tbl)

let assemble (p:prog) : exec =
  let (text_only_list, data_only_list) = split_text_data p ([],[]) in
  let text_sym_tbl = List.fold_left create_sym_entry [] text_only_list in
  let sym_tbl = List.fold_left create_sym_entry text_sym_tbl data_only_list in
  let text_seg = create_seg text_only_list sym_tbl in
  let data_seg = create_seg data_only_list sym_tbl in
  let data_bottom_addr = calc_data_bottom_addr text_sym_tbl in
  {entry = lbl_to_lit "main" sym_tbl; text_pos = mem_bot; data_pos = data_bottom_addr;  text_seg = text_seg; data_seg = data_seg}


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
