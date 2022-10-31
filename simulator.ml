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
    | _ -> ()
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
  (match x with
   Eq -> fz
  |Neq -> not fz
  |Ge -> (fs = fo)
  |Le -> (fz || fs <> fo)
  |Gt -> fs = fo && not fz
  |Lt -> fs <> fo
  )
  
(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option = 
    if addr < mem_bot then None
    else if (Int64.sub addr mem_bot) > mem_top then None
    else Some (Int64.to_int (Int64.sub addr mem_bot))

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

let set_cc_fz_fs (result: int64) (m : mach): unit =
    m.flags.fs <- (Int64.shift_right_logical(result)(63)) = Int64.one;
    m.flags.fz <- result = Int64.zero

let set_cc_fo (result: Int64_overflow.t) (m : mach): unit =
  let open Int64_overflow in (*should be add/mul/neg*)
  m.flags.fo <- result.Int64_overflow.overflow (*how to calc overflow*)


let get_indirectval (q: quad) (m: mach): int64 = (*rename get address val*)
  let address_o = map_addr q in 
    let address = match address_o with
        |Some x -> x
        |None -> raise X86lite_segfault
      in
      let ind_address = int64_of_sbytes [m.mem.(address + 0); m.mem.(address + 1);
                                         m.mem.(address + 2);m.mem.(address + 3);
                                         m.mem.(address + 4);m.mem.(address + 5);
                                         m.mem.(address + 6);m.mem.(address + 7)]
      in ind_address
  

let interpret_operand (oplist: operand list) (index: int) (m: mach): int64 =
  match (List.nth oplist index) with
            | Imm i ->  (* immediate *)
                (match i with
                        |Lit q -> q
                        |Lbl l -> failwith "label? in this economy?") 
            | Reg r ->   m.regs.(rind r)        (* register *)
            | Ind1 i->    (* indirect: displacement *)
                (match i with  
                         Lit q -> get_indirectval (q)(m) 
                       | Lbl l -> failwith "label? in this economy?")
            | Ind2 r ->    get_indirectval (m.regs.(rind r)) (m)  (*calculate val*) 
            | Ind3 (i,r) -> (* indirect: (%reg) *)
                (match i with       
                          Lit q -> get_indirectval( Int64.add m.regs.(rind r) q) (m)
                        | Lbl lbl -> failwith "label? in this economy?" )

(*let setcondition () = *)

let store_val_at_address (result:int64)(q:int64)(m:mach): unit=
  let address_o = map_addr q in 
    let address = match address_o with
      |Some x -> x
      |None -> raise X86lite_segfault
   in
   let sbyaddress : sbyte list = sbytes_of_int64 result 
  in 
    m.mem.(address + 0) <- List.nth sbyaddress 0;
    m.mem.(address + 1) <- List.nth sbyaddress 1;
    m.mem.(address + 2) <- List.nth sbyaddress 2;
    m.mem.(address + 3) <- List.nth sbyaddress 3;
    m.mem.(address + 4) <- List.nth sbyaddress 4;
    m.mem.(address + 5) <- List.nth sbyaddress 5;
    m.mem.(address + 6) <- List.nth sbyaddress 6;
    m.mem.(address + 7) <- List.nth sbyaddress 7

let  store_val (result:int64) (oplist : operand list) (ind: int) (m:mach) : unit =
  let dest_reg = List.nth oplist ind in 
    match dest_reg  with 
      |Imm i -> failwith "can't use an immediate"
      |Reg r -> m.regs.(rind r) <- result
      |Ind1 i -> (match i with 
                  | Lit q -> store_val_at_address (result) (q) (m)
                  | Lbl t -> failwith "label? in this economy?" 
                  )
      |Ind2 r ->  store_val_at_address (result) (m.regs.(rind r)) (m)
      |Ind3 (i,r) -> (match i with 
                      | Lit q -> store_val_at_address (result) ( Int64.add m.regs.(rind r) q) (m)
                      | Lbl t -> failwith "label? in this economy?" 
                      )
    

let arithmetic (op:opcode) (oplist:operand list) (m:mach): unit =
  (match op with 
    |Addq -> 
       let src = interpret_operand oplist 0 m in
       let dest = interpret_operand oplist 1 m in 
       let result = Int64_overflow.add src dest in
       store_val (result.value)(oplist)(1)(m);
       set_cc_fz_fs result.value m;
       set_cc_fo result m
    | Subq -> 
        let src = interpret_operand oplist 0 m in
        let dest = interpret_operand oplist 1 m in 
        let result = Int64_overflow.sub dest src in
        store_val (result.value)(oplist)(1)(m);
        (*print_string("sub called");print_newline();*)
        set_cc_fz_fs result.value m;
        set_cc_fo result m
    | Imulq -> 
        let src = interpret_operand oplist 0 m in
        let dest = interpret_operand oplist 1 m in 
        let result = Int64_overflow.mul src dest in
        store_val (result.value)(oplist)(1)(m);
        set_cc_fz_fs result.value m;
        set_cc_fo result m
    | Negq -> 
        let dest = interpret_operand oplist 0 m in 
        let result = Int64_overflow.neg dest in
        (store_val result.Int64_overflow.value oplist 0 m;
        set_cc_fz_fs result.value m;
        set_cc_fo result m;
        if dest = Int64.min_int then m.flags.fo <- true)
    | Incq -> 
        let dest = interpret_operand oplist 0 m in
        let result = Int64_overflow.succ dest in
        store_val (result.value)(oplist)(1)(m);
        set_cc_fz_fs result.value m;
        set_cc_fo result m
    | Decq -> 
        let dest = interpret_operand oplist 0 m in
        let result = Int64_overflow.pred dest in
        (*print_string("dec called");*)
        store_val (result.value)(oplist)(1)(m);
        set_cc_fz_fs result.value m;
        set_cc_fo result m
    | _ -> ()
  )

  let logic (op:opcode) (oplist:operand list) (m:mach): unit =
    (match op with 
      | Notq -> 
        let dest = interpret_operand oplist 0 m in
        let result = Int64.lognot dest in
        store_val (result)(oplist)(1)(m);
        set_cc_fz_fs result m;
        m.flags.fo <- false
      | Andq -> 
        let src = interpret_operand oplist 0 m in
        let dest = interpret_operand oplist 1 m in
        let result = Int64.logand src dest in
        store_val (result)(oplist)(1)(m);
        set_cc_fz_fs result m;
        m.flags.fo <- false
      | Orq -> 
        let src = interpret_operand oplist 0 m in
        let dest = interpret_operand oplist 1 m in
        let result = Int64.logor src dest in
        store_val (result)(oplist)(1)(m);
        set_cc_fz_fs result m;
        m.flags.fo <- false
      | Xorq -> 
        let src = interpret_operand oplist 0 m in
        let dest = interpret_operand oplist 1 m in
        let result = Int64.logxor src dest in
        store_val (result)(oplist)(1)(m);
        set_cc_fz_fs result m;
        m.flags.fo <- false
      | _ -> ()
      )

  let bitman (op:opcode) (oplist:operand list) (m:mach): unit =
  (match op with 
    | Sarq ->
      let amt = Int64.to_int (interpret_operand oplist 0 m) in
      let dest = interpret_operand oplist 1 m in 
      let result =  Int64.shift_right dest amt in
            store_val (result)(oplist)(1)(m);
            if amt = 0 then () else set_cc_fz_fs result m;  
            if amt = 1 then m.flags.fo <- false else ()
    | Shlq -> 
      let amt = Int64.to_int (interpret_operand oplist 0 m) in
      let dest = interpret_operand oplist 1 m in 
      let result = Int64.shift_left(dest) (amt) in
            (store_val (result)(oplist)(1)(m);
            if amt = 0 then () else set_cc_fz_fs result m;
            if (amt = 1) &&  
              ((Int64.shift_right_logical dest 63) <>  (Int64.shift_right_logical dest 62)) 
              then
                  m.flags.fo <- true
              else
                ())
    | Shrq -> 
      let amt = Int64.to_int (interpret_operand oplist 0 m) in 
      let dest = interpret_operand oplist 1 m in 
      let result = Int64.shift_right_logical dest amt in
      store_val result oplist 1 m;
      if amt = 0 then () 
      else if amt = 1 then m.flags.fo <- Int64.shift_right_logical dest 63 = Int64.one
      else ()
    | Set b -> 
      if interp_cnd {fo = m.flags.fo; fs = m.flags.fs ; fz = m.flags.fz} b 
        then store_val (Int64.one) (oplist) (0) (m) 
        else store_val (Int64.zero) (oplist) (0) (m)
    | _ -> ()
    )
  
  let push (oplist: operand list) (m: mach) :unit =
    (*print_string("push called");print_newline();*)
    (*let src = interpret_operand oplist 0 m in
    let opl = [Ind2 Rsp] in store_val_at_address src m.regs.(rind Rsp) m ;
    m.regs.(rind Rsp)<-Int64.sub m.regs.(rind Rsp) 8L  (*shifting instruction pointer*)
    (*store_val src opl 0 m *)(*need some function that lets you write values into memory, need to edit assign val*)*)
    let src = interpret_operand oplist 0 m in
    m.regs.(rind Rsp)<-Int64.sub m.regs.(rind Rsp) 8L;
    (*print_int(Int64.to_int (interpret_operand oplist 0 m)); print_newline();  *)
    let opl = [Ind2 Rsp] in store_val src opl 0 m
    (*print_int(Int64.to_int (interpret_operand oplist 0 m)); print_newline()*)
    

  let pop (oplist: operand list) (m : mach) : unit =
      (*let opl = [Ind2 Rsp] in
       let dest = interpret_operand oplist 0 m in
      let mem = (m.regs.(rind Rsp)) in 
      store_val (mem)(oplist)(1)(m); 
      m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L  (*shifting stack pointer*)*)
      let opl = [Ind2 Rsp] in
      let dest = interpret_operand opl 0 m in 
      store_val dest oplist 0 m;
      m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L

  let leaq(oplist: operand list)(m: mach): unit = 
    match (List.nth oplist 0) with
    | Ind1 i -> 
      (match i with 
      | Lit q -> store_val q oplist 1 m
      | Lbl s -> failwith "label? in this economy?"
      )
    | Ind2 r -> let q = (m.regs.(rind r)) in store_val q oplist 1 m
    | Ind3 (i, r)-> 
      (match i with 
      | Lit i -> let q = Int64.add i m.regs.(rind r) in store_val q oplist 1 m 
      | Lbl s -> failwith "label? in this economy?"
      )
      | _ -> failwith "must be an indirect operand"

  let datamove (op:opcode) (oplist:operand list) (m:mach): unit =
  (match op with 
    | Leaq ->  leaq oplist m
    | Movq -> 
      let src = interpret_operand oplist 0 m in
      let dest = interpret_operand oplist 1 m in 
      (*print_string("mov called");print_newline();
      print_int(Int64.to_int (interpret_operand oplist 0 m)); print_int(Int64.to_int (interpret_operand oplist 1 m));print_newline();*)
      store_val src oplist 1 m
    | Pushq -> push oplist m
    | Popq -> pop oplist m
    | _ -> ()
        )


  let increment_rip(m: mach): unit =
      m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L

  let controlflow (op:opcode) (oplist:operand list) (m:mach): unit =
  (match op with 
    | Cmpq ->
      let src = interpret_operand oplist 0 m in
      let dest = interpret_operand oplist 1 m in
      let result = Int64.sub dest src in
      (*print_string("cmp called");print_newline();*)
      set_cc_fz_fs result m;
      if src = Int64.min_int then m.flags.fo <- true else m.flags.fo <- false;
    | Jmp -> 
      let src = interpret_operand oplist 0 m in 
      m.regs.(rind Rip) <- src
    | Callq -> 
         (*changed this as well to 8*)
        (*print_string("call called");print_newline();*)
        m.regs.(rind Rip)<-(Int64.add m.regs.(rind Rip) 8L);
        let rip1 = [Reg Rip] in
        push rip1 m;
        m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L;
        let src = interpret_operand oplist 0 m in 
        m.regs.(rind Rip) <- src;
        m.regs.(rind Rip)<-Int64.sub m.regs.(rind Rip) 8L
    | Retq -> 
        let rip1 = [Reg Rip] in 
          pop rip1 m
    | J cc -> 
      let src = interpret_operand oplist 0 m in
      (*print_string("jump called");print_newline();*)
      if interp_cnd {fo = m.flags.fo; fs = m.flags.fs ; fz = m.flags.fz} cc 
        then m.regs.(rind Rip) <- src
        else ()(*m.regs.(rind Rip)<-(Int64.add m.regs.(rind Rip) 8L))*) (*eight?*)
    | _ -> ()
  )
  

  let interpret_sbyte (intr: ins) (m: mach): unit =
  match intr with 
  |(op, oplist) ->
  match op with 
  (* data movement*)
  | Leaq | Movq | Pushq | Popq -> datamove op oplist m
  (* logic*)
  | Notq | Andq | Orq | Xorq -> logic op oplist m
  (* arithmetic*)
  | Addq | Subq | Imulq | Incq | Decq | Negq -> arithmetic op oplist m
  (* bit-manipulation*)
  | Shlq | Sarq | Shrq | Set _ -> bitman op oplist m
  (* control flow and condition*)
  | Cmpq | Jmp | Callq| Retq | J _ -> controlflow op oplist m    

  let step (m:mach) : unit =
    let instruction = m.regs.(rind Rip) in
    (*print_string("rip counter: "); print_endline(Int64.to_string m.regs.(rind Rip)); *)
    (*print_string("rsp counter: "); print_endline(Int64.to_string m.regs.(rind Rsp)); *)
    let address_o = map_addr instruction in 
    let address = 
    match address_o with 
    | Some x-> x
    | None -> raise X86lite_segfault
    in 
    let information = m.mem.(address) in 
    match information with 
    | InsB0 instr -> (interpret_sbyte instr m; increment_rip m)
    | InsFrag -> ()
    | Byte b -> ()  


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

    (* Main Assemble program *)
   
type symbol = (lbl * quad)
type symbollist = symbol list


let rec findlbl (s: symbol list ) (l : lbl) (flag : int): int64 = 
  (match s with
      |[] -> if flag = 0 then -1L else raise (Undefined_sym (l))
      |(lbl,quad) :: t -> if l = lbl then quad else findlbl t l flag
  )

let makesymlist (flag : int)((symlist, size):(symbol list) * int64) (e : elem) : (symbol list * int64) = 
  (*going to see if lbl already exists, if not return error*)
    let rec datalist (dsize : int64) (d : data) : int64 =
      (match d with
        |Asciz a -> Int64.add dsize (Int64.of_int((String.length a)+1));
        |Quad q -> Int64.add dsize (8L))
    in    
      (match(flag, e.asm) with
          | (0, Text t) -> 
                          let addr = Int64.add size (Int64.of_int((List.length t)* 8)) in (*not even sure this is ever called in the tests*)
                          let add = findlbl symlist e.lbl 0 in
                            if add = (-1L) then 
                              (List.append (symlist) [ ((e.lbl), size)], addr)
                          else raise (Redefined_sym (e.lbl))
                          
          | (1, Data d) -> let add = findlbl symlist e.lbl 0 in
                            if add = (-1L) then
                              let addr = Int64.add size (List.fold_left datalist 0L d) in
                              (List.append (symlist) [ ((e.lbl), size) ], addr)
                            else raise (Redefined_sym (e.lbl))
          |(_,_) -> symlist, size
        )

let rec resolve_operands (sl : symbol list) (op : operand list) : operand list =       
  match op with
  |Imm i::t -> (match i with
              |Lbl l -> List.append [Imm (Lit ((findlbl sl l 1)))] (resolve_operands (sl) (t))
              |_ -> List.append [Imm i] (resolve_operands (sl) (t)) ) 
  | Ind1 i::t -> (match i with
              |Lbl l -> List.append [Ind1 (Lit ((findlbl sl l 1)))] (resolve_operands (sl) (t))
              |_ -> List.append [Ind1 i] (resolve_operands (sl) (t)) )   
  | Ind3 (i,r)::t -> (match i with
              |Lbl l -> List.append [Ind3 ((Lit ((findlbl sl l 1))), r)] (resolve_operands (sl) (t))
              |_ -> List.append [Ind3 (i,r)] (resolve_operands (sl) (t)) )   
  |r::t -> List.append [r] (resolve_operands (sl) (t))
  |[] -> []


let resolveins (sl : symbollist) (sbl: sbyte list) (i: ins) : sbyte list = 
  match i with
    (opcode, operand) -> List.append sbl (sbytes_of_ins (opcode, (resolve_operands sl operand)  ))

let resolvedata (sl : symbol list) (sbl : sbyte list) (d: data): sbyte list  = 
  (match d with 
      |Asciz s -> List.append sbl (sbytes_of_data(d))
      |Quad i ->  match i with
                      |Lit q -> List.append sbl (sbytes_of_data d)
                      |Lbl l -> List.append sbl (sbytes_of_data (Quad (Lit (findlbl sl l 1) )))
  )
  
  let resolvelbls (opt : int) (sl : symbol list) (sbl : sbyte list) (e : elem) :
  sbyte list =
  let resolvedi = resolveins sl in
  let resolvedd = resolvedata sl
  in
    match (opt, (e.asm)) with
    | (0, Text t) -> List.append sbl (List.fold_left resolvedi [] t)
    | (1, Data d) -> List.append sbl (List.fold_left resolvedd [] d)
    | (_, _) -> sbl


let  getsize (flag: int) (size:int64) (e : elem): int64 = (
  let rec datalist (dsize : int64) (d : data) : int64 =
    (match d with
      |Asciz a -> Int64.add dsize (Int64.of_int((String.length a)+1))
      |Quad q -> Int64.add dsize (8L))
    in    
    (match(flag, e.asm) with
        | (0, Text t) -> Int64.add size (Int64.of_int ((List.length t) * 8))
        | (1, Data d) -> Int64.add size (List.fold_left datalist 0L d )
        |(_,_) -> size)
)


      let assemble (p:prog) : exec =
        (*get the size of the data*)
        let datasize = List.fold_left (getsize 0) 0L p in
        (*make the symbol list*)
        let slt =  makesymlist 0 in
        let sld =  makesymlist 1 in
        let (symb, sized) = List.fold_left slt ([], 0x400000L) p in
        let (esymb, sizedt) = List.fold_left sld (symb, sized) p in
        (*find starting address*)
        let e_address = findlbl symb "main" 1 in
        let resolve_text = resolvelbls 0 esymb in 
        let resolve_data = resolvelbls 1 esymb  in
        (*fix labels in text and data*)
        let listtext = List.fold_left (resolve_text) ([]) (p) in 
        let listdata = List.fold_left (resolve_data) [] p in 
            { entry    = e_address;              (* address of the entry point *)
              text_pos = 0x400000L;             (* starting address of the code *)
              data_pos = Int64.add 0x400000L datasize;            (* starting address of the data *)
              text_seg = listtext;       (* contents of the text segment *)
              data_seg = listdata        (* contents of the data segment *)
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
    let mem_arrayi = Array.make 0xFFF8 InsFrag in 
    let text_array = Array.of_list text_seg in 
    let data_array = Array.of_list data_seg in
    let text_and_data = Array.append text_array data_array in
    Array.blit (text_and_data) (0) (mem_arrayi) (0) (Array.length text_and_data);  (*might need to multiply*) 
    let exit_address = Array.of_list (sbytes_of_int64 exit_addr) in
   (*print_string("exit_address "); print_int(Int64.to_int exit_addr);*)
    let mem_array = Array.append mem_arrayi exit_address in
    let mem = mem_array in
    let flags = {fo = false; fs = false; fz = false} in
    let regs = Array.make 17 0L in
    Array.set regs (rind Rip) entry; 
    Array.set regs (rind Rsp) 0x40FFF8L; (*1 past the last bit in memory*)
    {flags = flags; regs = regs; mem = mem}

