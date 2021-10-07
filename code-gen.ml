#use "semantic-analyser.ml";;
open Semantics;;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)

   
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string

  val rename : expr' list -> expr' list

end;;

exception Debug of sexpr;;
exception Debug2 of string;;






module Code_Gen : CODE_GEN = struct

  let tags = ref [];;
  let lexit_counter = ref 0;;
  let lelse_counter = ref 0;;
  let applic_counter = ref 0;;
  let params_loop_counter = ref 0;;
  let set_major_counter = ref 0;;
  let label_counter = ref 0;;
  let lcode_counter = ref 0;;
  let lcont_counter = ref 0;;
  let create_lst_counter = ref 0;;
  let kill_magic_counter = ref 0;;
  let finish_counter = ref 0;;
  let adjust_stack_counter = ref 0;;

  let rename exprlist = 
  let nameMap = ref [] in
  let rec scan asts = 
    (match asts with|[]->[]
                    |car::cdr-> let newExp = (rename_aux car) in (setFalse !nameMap);[newExp]@(scan cdr))

      and tag_handler name = 
         let tupple = (List.find_opt (fun(x) -> match x with |(n,counter,b)-> if (n = name) then true else false) !nameMap) in
                      let counter = (match tupple with
                                    |Some((n,counter,bool))-> counter
                                    |None->ref 0) in
                      let bool = (match tupple with
                                    |Some((n,counter,bool))-> bool
                                    |None->ref true) in
                      if (!counter=0) then ((nameMap:=!nameMap@[(name,ref 1,ref true)]);(String.concat "" [name;"1"]))
                                      else (if (!bool) then (String.concat "" [name;(string_of_int !counter)])
                                            else ((counter :=!counter+1);bool:=true;(String.concat "" [name;(string_of_int !counter)])))

            
      and const_handler sexpr = 
          match sexpr with
            | Bool(e) -> sexpr
            | Nil -> Nil
            | Number(e) -> sexpr
            | Char(e) -> sexpr
            | String(e) -> sexpr
            | Symbol(e) -> sexpr
            | Pair(e1,e2) -> let car = (const_handler e1) in Pair(car,const_handler e2)
            | TaggedSexpr(name, exp) -> let newName = (tag_handler name) in 
                                            TaggedSexpr(newName,(const_handler exp))
            | TagRef(name) -> TagRef(tag_handler name)

      and rename_aux expr = 
          match expr with 
            | Const'(Void) -> expr
            | Const'(Sexpr(e)) -> Const'(Sexpr(const_handler e))
            | Var'(e) -> expr 
            | Box'(e) -> expr
            | BoxGet'(e) -> expr
            | BoxSet'(var,exp) -> BoxSet'(var,(rename_aux exp))
            | If'(t,th,el) -> let tst =(rename_aux t) in
                              let thn =(rename_aux th) in 
                              If'(tst,thn,(rename_aux el))
            | Seq'(eList) -> Seq'(List.map (rename_aux) eList)
            | Set'(var,value) -> Set'(rename_aux var,rename_aux value)
            | Def'(var,value) -> Def'(rename_aux var,rename_aux value)
            | Or'(eList) -> Or'(List.map (rename_aux) eList)
            | LambdaSimple'(params,body) -> LambdaSimple'(params, (rename_aux body))
            | LambdaOpt'(params,optList,body) -> LambdaOpt'(params,optList, (rename_aux body))
            | Applic'(exp,eList) -> let op = (rename_aux exp) in Applic'(op, (List.map (rename_aux) eList))
            | ApplicTP'(exp,eList) -> let op = (rename_aux exp) in ApplicTP'(op, (List.map (rename_aux) eList))

      and setFalse list = 
          (match list with|[]-> ()
                          |car::cdr-> (match car with|(n,counter,b) -> b:=false;(setFalse cdr)))

      in scan exprlist;;


  let make_consts_tbl asts = 
  let tagDefs = ref [] in
  let const_table = ref [(Void,(0,"MAKE_VOID"));(Sexpr(Nil), (1, "MAKE_NIL"));(Sexpr(Bool false),(2,"MAKE_BOOL(0)"));(Sexpr(Bool true),(4,"MAKE_BOOL(1)"))] in
  let offset = ref 6 in
  let rec scan constTable expr= 
    match expr with 
      (* | Const'(Void) -> (constTable:=!constTable@[(Void,(!offset,"MAKE_VOID"))]);offset:=!offset+1;() *)
      | Const'(Void) -> ()
      | Const'(Sexpr(e)) ->(sexpHandler e constTable);()
      | Var'(e) -> ()
      | Box'(e) -> ()
      | BoxGet'(e) -> ()
      | BoxSet'(var,exp) -> (scan constTable exp)
      | If'(t,th,el) -> (scan constTable t);(scan constTable th);(scan constTable el);()
      | Seq'(eList) -> (retUnit (List.map (scan constTable) eList));()
      | Set'(var,value) -> (scan constTable value);()
      | Def'(var,value) -> (scan constTable value);()
      | Or'(eList) -> (retUnit (List.map (scan constTable) eList));()
      | LambdaSimple'(params,body) -> (scan constTable body);()
      | LambdaOpt'(params,optList,body) -> (scan constTable body);()
      | Applic'(exp,eList) -> (retUnit2 (scan constTable exp));(retUnit (List.map (scan constTable) eList));()
      | ApplicTP'(exp,eList) -> (retUnit2 (scan constTable exp));(retUnit (List.map (scan constTable) eList));()
      
  and sexpHandler exp const_tbl = 
    match exp with
      | Bool(e)->()
      | Nil->()
      | Number(e) -> if(isMember exp !const_tbl) then () 
                     else (match e with
                        |Int(num)-> let s=(Printf.sprintf ("MAKE_LITERAL_INT(%d)") num) in (const_tbl:=!const_tbl@[(Sexpr(Number(Int(num))), (!offset, s))]);offset:=!offset+9;()
                        |Float(num)-> let s=(Printf.sprintf ("MAKE_LITERAL_FLOAT(%f)") num) in (const_tbl:=!const_tbl@[(Sexpr(Number(Float(num))), (!offset, s))]);offset:=!offset+9;())
      | Char(e) -> if(isMember exp !const_tbl) then () 
                   else let s =(Printf.sprintf ("MAKE_LITERAL_CHAR(%d)") (Char.code e)) in ((const_tbl:=!const_tbl@[(Sexpr(exp), (!offset, s))]);offset:=!offset+2;())
      | String(e) -> if(isMember exp !const_tbl) then () 
                    else let s = (Printf.sprintf ("MAKE_LITERAL_STRING\"%s\"") e) in ((const_tbl:=!const_tbl@[(Sexpr(exp), (!offset, s))]);offset:=!offset+(String.length e)+9;())
      | Symbol(e) -> (sexpHandler (String(e)) const_tbl);
                     if(isMember exp !const_tbl) then ()
                     else (let offsetNum = (getOffset (String(e)) !const_tbl) in let s=(Printf.sprintf ("MAKE_LITERAL_SYMBOL(const_tbl+%d)") offsetNum) in 
                     (const_tbl:=!const_tbl@[(Sexpr(exp), (!offset, s))]);offset:=!offset+9;())
      | Pair(e1,e2) -> ((sexpHandler e1 const_tbl);
                       (sexpHandler e2 const_tbl);
                       if(isMember exp !const_tbl) then ()
                       else let carOffset = (getOffset e1 !const_tbl) in let cdrOffset = (getOffset e2 !const_tbl) in
                            let s = (Printf.sprintf ("MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)") carOffset cdrOffset) in
                            (const_tbl:=!const_tbl@[(Sexpr(exp), (!offset, s))]);offset:=!offset+17;())

      | TaggedSexpr(name, exp) -> tagDefs:=!tagDefs@[(name,exp)];(sexpHandler exp const_tbl);()
      | TagRef(name) -> ()

  and isMember exp list = (match list with              (*maybe need to use sexpr_eq instead*)
                  |[]->false
                  |car::cdr-> (match car with|(Sexpr(e),(_,_))->(if (e=exp) then true else (isMember exp cdr))|_-> (isMember exp cdr)))

  and getOffset exp list =  let newExp = (match exp with| TaggedSexpr(name,e)->e|_->exp) in
                            (match list with
                            (* |[]-> raise (Debug(exp)) *)
                            (* |[(Void,(_,_))]-> raise Debug2 *)
                            |[]-> (-1)   (*-1 will be returned only for tagrefs during second pass, and then overwritten during third pass *)
                            |car::cdr-> (match car with|(Sexpr(expr),(item_offset,_))-> (if (expr=newExp) then item_offset else (getOffset newExp cdr))|_-> (getOffset newExp cdr)))

  and retUnit exp = ()
  and retUnit2 exp = ()

  and refResolve const_tbl newConstbl = 
    (match (const_tbl) with|[] -> !newConstbl
                           |car::cdr-> (match car with
                                      |(Sexpr(Pair(TagRef(a),TagRef(b))),(offset_num, s))-> 
                                        let offset1 = (handleRef a !tagDefs) in
                                        let offset2 = (handleRef b !tagDefs) in
                                        let newString = (Printf.sprintf ("MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)") offset1 offset2) in
                                        let res = (Sexpr(Pair(TagRef(a),TagRef(b))),(offset_num,newString)) in
                                        (newConstbl:=!newConstbl@[res]);(refResolve cdr newConstbl)
                                      |(Sexpr(Pair(TagRef(a),notRef)),(offset_num, s))->
                                        let offset1 = (handleRef a !tagDefs) in
                                        let notRefOffset = (List.nth (String.split_on_char ',' s) 1) in
                                        let newString = (Printf.sprintf ("MAKE_LITERAL_PAIR(const_tbl+%d,%s") offset1 notRefOffset) in
                                        let res = (Sexpr(Pair(TagRef(a),notRef)),(offset_num, newString)) in
                                        (newConstbl:=!newConstbl@[res]);(refResolve cdr newConstbl)
                                      |(Sexpr(Pair(notRef,TagRef(a))),(offset_num, s))->
                                        let notRefOffset = (List.nth (String.split_on_char ',' s) 0) in
                                        let offset2 = (handleRef a !tagDefs) in
                                        let newString = (Printf.sprintf ("%s, const_tbl+%d)") notRefOffset offset2) in
                                        let res = (Sexpr(Pair(notRef,TagRef(a))),(offset_num, newString)) in
                                        (newConstbl:=!newConstbl@[res]);(refResolve cdr newConstbl)
                                      |const-> (newConstbl:=!newConstbl@[const]);(refResolve cdr newConstbl)))
                                      
  and handleRef tagRefName tag_defs= 
    (match tag_defs with|[]-> raise X_this_should_not_happen
                       |car::cdr-> (match car with
                                      |(tagName,exp)->if (tagName = tagRefName) 
                                                      then (getOffset exp !const_table) 
                                                      else (handleRef tagRefName cdr)))

in let res = (List.map (scan const_table) (rename asts)) in (retUnit res);(tags:=!tags@(!tagDefs));(refResolve !const_table (ref []));;

let make_fvars_tbl asts = 
  let prim_names = 
  ["boolean?"; "float?"; "integer?"; "pair?";
   "null?"; "char?"; "string?";
   "procedure?" ; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "symbol->string"; "char->integer";"integer->char";
   "eq?"; "+"; "*"; "-"; "/"; "<"; "="; "car";"cdr";"cons";"set-car!";"set-cdr!";"apply"] in
  let retUnit exp = () in
  let freeVar_table = ref [] in
  let index = ref 0 in
  let rec scan fv_table count exps = 
      (match exps with 
            |car::cdr -> (match car with |Def'(Var'(VarFree(name)),_) -> (fv_table := !fv_table@[(name,!count)]; count := !count+1;
                                                                        (scan fv_table count cdr))
                                         |_->(scan fv_table count cdr))
            |_ -> ())
  in ((scan freeVar_table index asts);
     (retUnit (List.map (fun x-> (freeVar_table := !freeVar_table@[(x,!index)]; index := !index+1;)) prim_names)) ;!freeVar_table);;
  


 
let generate consts fvars e = 
let string = ref "" in
let rec scanExp fParamsLen depth consts_tbl fvars_tbl exp = 
    (match exp with

      |Const'(c)-> let c = (match c with |Sexpr(TaggedSexpr(name,exp)) -> Sexpr(exp)
                                         |Sexpr (TagRef(name))-> (findInTagDefs name !tags)
                                         |_-> c) in        
                   let address = (addressInConstTable consts_tbl c) in 
                   let addition = (Printf.sprintf ("mov rax,%s\n") address) in string := !string ^ addition

      |Var'(VarParam(_, minor))-> string:=!string ^ (Printf.sprintf ("mov rax, qword [rbp + 8 * (4 + %d)]\n") minor)

      |Set'(Var'(VarParam(_, minor)),value)-> ((scanExp fParamsLen depth consts_tbl fvars_tbl value);
                                              (string:=!string ^ (Printf.sprintf ("mov qword [rbp + 8 * (4 + %d)], rax\n") minor) ^ "mov rax, SOB_VOID_ADDRESS\n"))

      |Var'(VarBound(_, major, minor))-> 
        string:=!string ^ "mov rax, qword [rbp + 8 * 2]\n" ^ (Printf.sprintf ("mov rax, qword [rax + 8 * %d]\n") major) ^ (Printf.sprintf("mov rax, qword [rax + 8 * %d]\n") minor)

      |Set'(Var'(VarBound(_,major,minor)),value)-> 
          ((scanExp fParamsLen depth consts_tbl fvars_tbl value);
          (string:=!string ^ "mov rbx, qword [rbp + 8 * 2]\n" ^ (Printf.sprintf ("mov rbx, qword [rbx + 8 * %d]\n") major) ^ (Printf.sprintf("mov qword [rbx + 8 * %d], rax\n") minor) ^ "mov rax, SOB_VOID_ADDRESS\n"))

      |Var'(VarFree(v))-> (let location = (labelInFVarTable fvars_tbl v) in
                            let addition = (Printf.sprintf ("mov rax, qword [fvar_tbl+ (WORD_SIZE * %d)]\n") location) in string := !string ^ addition)

      |Set'(Var'(VarFree(v)),value)-> 
          let location = (labelInFVarTable fvars_tbl v) in
          ((scanExp fParamsLen depth consts_tbl fvars_tbl value);
           (string:=!string ^ (Printf.sprintf ("mov qword [fvar_tbl+ WORD_SIZE * %d], rax\n") location) ^ "mov rax, SOB_VOID_ADDRESS\n"))

      |Seq'(expList)-> let res = (List.map (scanExp fParamsLen depth consts_tbl fvars_tbl) expList) in (retUnit res)
      |Or'(expList)-> (handleOr fParamsLen depth consts_tbl fvars_tbl expList)
      |If'(ts,th,el)-> (handleIf fParamsLen depth consts_tbl fvars_tbl ts th el)

      |Box'(v)-> (((scanExp fParamsLen depth consts_tbl fvars_tbl (Var'(v)));
                 (string := !string ^ "mov r12, rax\n" ^ "MALLOC rax, WORD_SIZE\n" ^ "mov [rax], r12\n")))

      |BoxGet'(v) -> ((scanExp fParamsLen depth consts_tbl fvars_tbl (Var'(v)));
                      (string := !string ^ "mov rax, qword [rax]\n"))
                      
      |BoxSet'(v,value) ->  ((scanExp fParamsLen depth consts_tbl fvars_tbl value);
                             (string := !string ^ "push rax\n");
                             (scanExp fParamsLen depth consts_tbl fvars_tbl (Var'(v)));
                             (string := !string ^ "pop qword [rax]\n" ^ "mov rax, SOB_VOID_ADDRESS\n"))
                                           
      |Def'(Var'(VarFree(v)),value)-> 
          let location = (labelInFVarTable fvars_tbl v) in
          ((scanExp fParamsLen depth consts_tbl fvars_tbl value);
           (string:=!string ^ (Printf.sprintf ("mov qword [fvar_tbl+ WORD_SIZE * %d], rax\n") location) ^ "mov rax, SOB_VOID_ADDRESS\n"))
 
      |Applic'(proc,argsList)-> 
        (string := !string ^ "push 0\n");   (*push magic *)
        (match proc with |LambdaSimple'(p,body) -> (if ((List.length p) = (List.length argsList)) 
                                                  then () else raise (Debug2 "call lambda with wrong num of args"))
                                                  
                         
                         |LambdaOpt'(pList,optList,lBody) -> (if ((List.length pList) > (List.length argsList))
                                                              then raise (Debug2 "call lambda opt with wrong num of args") else ())
                                                            
                         |_->());

        (processArgs fParamsLen depth consts_tbl fvars_tbl (List.length argsList) (List.rev argsList));                             
        ((scanExp fParamsLen depth consts_tbl fvars_tbl proc);
        (string:=!string ^ "cmp TYPE(rax), T_CLOSURE\n"
                         ^ "je " ^ (Printf.sprintf ("Cont%d\n") !applic_counter));
        (string:=!string ^ "mov rax, 1\n" ^ "mov rbx, 1\n" ^ "int 0x80\n" );
        (string:=!string ^ (Printf.sprintf ("Cont%d:\n") !applic_counter));(applic_counter:=!applic_counter+1);
        (string:=!string ^ "push GET_ENV(rax)\n" ^ "call GET_BODY(rax)\n");
        (string:=!string ^ "add rsp , 8*1 ; pop env\n" ^ 
                           "pop rbx ; pop arg count\n" ^ 
                           "shl rbx , 3 ; rbx = rbx * 8\n"  ^
                           "add rsp , rbx ; pop args\n" ^ "add rsp, 8\n"))


      

      |LambdaSimple'(p,body) -> let lcode_count = !lcode_counter in
                                let lcont_count = !lcont_counter in
                                 (lcode_counter:= !lcode_counter+1);
                                 (lcont_counter:= !lcont_counter+1);
                                 let tmp = if(depth=(-1)) then "mov rbx, SOB_NIL_ADDRESS\n"
                                           else (extEnv_aux fParamsLen depth) ^ "mov rbx,rax\n" in 
                                  string := !string ^ tmp 
                                 ^ (Printf.sprintf ("MAKE_CLOSURE(rax, rbx, Lcode%d)\n") lcode_count)
                                 ^ (Printf.sprintf ("jmp Lcont%d\n") lcont_count)
                                 ^ (Printf.sprintf ("Lcode%d:\n") lcode_count)
                                 ^ "push rbp\n"
                                 ^ "mov rbp, rsp\n";
                                (scanExp (List.length p) (depth+1) consts_tbl fvars_tbl body);
                                 string:= !string ^ "leave\n" ^ "ret\n"
                                 ^(Printf.sprintf ("Lcont%d:\n") lcont_count)

      |LambdaOpt'(pList,optList,lBody) -> let lcode_count = !lcode_counter in
                                          let lcont_count = !lcont_counter in
                                          (lcode_counter:= !lcode_counter+1);
                                          (lcont_counter:= !lcont_counter+1);
                                          let tmp = if(depth=(-1)) then "mov rbx, SOB_NIL_ADDRESS\n"
                                                    else (extEnv_aux fParamsLen depth) ^ "mov rbx,rax\n" in 
                                            string := !string ^ tmp 
                                          ^ (Printf.sprintf ("MAKE_CLOSURE(rax, rbx, Lcode%d)\n") lcode_count)
                                          ^ (Printf.sprintf ("jmp Lcont%d\n") lcont_count)
                                          ^ (Printf.sprintf ("Lcode%d:\n") lcode_count);
                                          (adjust_stack (List.length pList));
                                           string := !string ^ "push rbp\n" ^ "mov rbp, rsp\n" ;
                                          
                                          (scanExp ((List.length pList)+1) (depth+1) consts_tbl fvars_tbl lBody);
                                          string:= !string ^ "leave\n" ^ "ret\n"
                                          ^(Printf.sprintf ("Lcont%d:\n") lcont_count)

       |ApplicTP'(proc,args) -> (string := !string ^ "push 0\n");   (*push magic *)
                                (processArgs fParamsLen depth consts_tbl fvars_tbl (List.length args) (List.rev args)); 
                                (scanExp fParamsLen depth consts_tbl fvars_tbl proc);
                                (string:=!string ^ "cmp TYPE(rax), T_CLOSURE\n"
                                ^ "je " ^ (Printf.sprintf ("Cont%d\n") !applic_counter));
                                (string:=!string ^ "mov rax, 1\n" ^ "mov rbx, 1\n" ^ "int 0x80\n" );
                                (string:=!string ^ (Printf.sprintf ("Cont%d:\n") !applic_counter))
                                ;(applic_counter:=!applic_counter+1);
                                (string:=!string ^ "push GET_ENV(rax)\n" 
                                ^ "push qword [rbp + 8 * 1]\n"
                                ^ (Printf.sprintf ("mov rdx, 32 + (%d*8)\n")(List.length args))
                                ^ "mov rsi, [rbp +24]\n" ^ "shl rsi, 3\n" ^ "mov rbx, rsi\n" ^ "add rbx, 40\n"
                                ^ "mov rcx, rbx\n" ^ "sub rcx, rdx\n"
                                ^ "mov rdi, rbp\n" ^ "add rdi, rcx\n"
                                ^ "mov rbp, [rbp]\n" ^ "mov rsi, rsp\n" ^ "mov r12, rax\n"
                                ^ "call memmove\n" ^ "mov rsp,rax\n"
                                ^ "mov rax, r12\n"
                                ^ "jmp GET_BODY(rax)\n"
                                ^ "add rsp , 8*1 ; pop env\n"  
                                ^ "pop rbx ; pop arg count\n"  
                                ^ "shl rbx , 3 ; rbx = rbx * 8\n"  
                                ^ "add rsp , rbx ; pop args\n" ^ "add rsp, 8\n")


      
      
    



      |_-> raise X_not_yet_implemented
    )



      and extEnv_aux fPLen depth = 
        let ribs_ptr = (Printf.sprintf ("MALLOC rax, (%d*WORD_SIZE)\n")  (1 + depth)) in
        let new_vector = (Printf.sprintf ("MALLOC r10, (%d*WORD_SIZE)\n")  fPLen) in
        let copy_params = (if (fPLen <> 0) then (copyStackParams fPLen "") else "mov r10, 0\n") in
        let copy_env = "mov [rax],r10\n" ^ "mov rsi,1\n" ^ (Printf.sprintf ("mov rcx, %d\n") depth) ^ "mov rbx, [rbp+16]\n"  
                             ^ (Printf.sprintf ("Set_major%d:\n") !set_major_counter); in 
        let cmp_depth = "cmp rcx, 0\n" ^ (Printf.sprintf ("je Label%d\n") (!label_counter)) in
        let steal_pointer = "mov rdx,[rbx + ((rsi-1)*WORD_SIZE)]\n" ^ "mov [rax + (rsi*WORD_SIZE)], rdx\n"
                                  ^ "inc rsi\n" ^ (Printf.sprintf ("loop Set_major%d\n") !set_major_counter) in 
        let exit =(Printf.sprintf ("Label%d:\n") !label_counter) in
        (set_major_counter:=!set_major_counter+1);
        (label_counter:=!label_counter+1);
        (ribs_ptr ^ new_vector ^copy_params ^ copy_env ^ cmp_depth ^ steal_pointer ^ exit)
       

      and copyStackParams paramNum accString = 
        if (paramNum = 0)
        then accString
        else (copyStackParams (paramNum-1) 
              (accString ^ (Printf.sprintf ("mov rdx, [rbp + 32 + (%d - 1)*WORD_SIZE]\n") paramNum) ^
              (Printf.sprintf ("mov [r10 + (%d - 1)*WORD_SIZE], rdx\n") paramNum)))


        

    and addressInConstTable const_tbl c =
      (match const_tbl with|[]-> raise (Debug2 "error in addressInConstTable - have to fix with tagDefs method")
                           |car::cdr -> (match car with
                                          |(const,(offset,_))-> (if (const=c) 
                                                                       then (Printf.sprintf ("(const_tbl+%d)") offset)
                                                                       else (addressInConstTable cdr c))))
                                        
    and labelInFVarTable free_tbl fVar =
      (match free_tbl with|[]->raise X_this_should_not_happen
                          |car::cdr->(match car with|(name,index)->if(name=fVar) then index else (labelInFVarTable cdr fVar)))
    
    and retUnit exp = ()
    and retUnit2 exp = ()

    and handleOr fParamLen depth cList fList lst =
      (* let lexit_count = !lexit_counter in *)
      (match lst with|[]-> ()
                     |car::cdr-> ((scanExp fParamLen depth cList fList car);
                                  (if (cdr=[]) 
                                  then ((string:=!string ^ (Printf.sprintf ("Lexit%d:\n") !lexit_counter));lexit_counter:=!lexit_counter+1)
                                  else (string:=!string ^ "cmp rax, SOB_FALSE_ADDRESS\n" ^
                                        (Printf.sprintf ("jne Lexit%d\n") !lexit_counter);(handleOr fParamLen depth cList fList cdr)))))
                            
    and handleIf fParamLen depth cList fList ts th el =
        (* let lelse_count = !lelse_counter in *)
        (* let lexit_count = !lexit_counter in *)
        ((scanExp fParamLen depth cList fList ts);
        (string:=!string ^ "cmp rax, SOB_FALSE_ADDRESS\n" ^ (Printf.sprintf ("je Lelse%d\n") !lelse_counter));
        (scanExp fParamLen depth cList fList th);
        (string:=!string ^ (Printf.sprintf ("jmp Lexit%d\n") !lexit_counter) ^ (Printf.sprintf ("Lelse%d:\n") !lelse_counter));
        (lelse_counter:=!lelse_counter+1);
        (scanExp fParamLen depth cList fList el);
        (string:=!string ^ (Printf.sprintf ("Lexit%d:\n") !lexit_counter));
        (lexit_counter:=!lexit_counter+1))


    and findInTagDefs refName tags_list= 
      (match tags_list with|[]->raise X_this_should_not_happen
                           |car::cdr->(match car with|(name,exp)->if (name=refName) 
                                                                  then Sexpr(exp)
                                                                  else (findInTagDefs refName cdr)))
    and processArgs fParamLen depth cList fList n argList = 
      (match argList with |[]->(string:=!string ^ (Printf.sprintf ("push %d\n") n))
                          |car::cdr-> ((scanExp fParamLen depth cList fList car);
                                       (string:=!string ^ "push rax\n");
                                       (processArgs fParamLen depth cList fList n cdr)))


    and adjust_stack pList_len  =
      let create_lst_count = !create_lst_counter in
      let kill_magic_count = !kill_magic_counter in
      let finish_count = !finish_counter in
      let adjust_stack_count = !adjust_stack_counter in
      let label_count = !label_counter in
      string := !string ^ "mov rdx, [rsp + 16]\n"
      ^"mov rsi, rdx\n" ^ (Printf.sprintf ("sub rsi , %d\n") pList_len)  ^ "mov rcx, rsi\n"
      ^ "cmp rcx , 0\n" ^ (Printf.sprintf ("je kill_magic%d\n") kill_magic_count)
      ^ "mov rsi, rdx\n"^ "dec rsi\n"   
      ^ "shl rsi ,3\n" ^ "lea rbx, [rsp+24+rsi]\n" ^ "mov rsi,0\n"
      ^ "mov r11, [rbx]\n" ^ "MAKE_PAIR(r10, r11, SOB_NIL_ADDRESS)\n" ^ "dec rcx\n" ^ "add rsi, 8\n"
      ^ "cmp rcx, 0\n" ^  (Printf.sprintf ("je Label%d\n") label_count) 
      ^ (Printf.sprintf ("create_lst%d:\n") create_lst_count) 
      ^ "mov r12, r10\n" ^ "mov rdi, rbx\n"^ "sub rdi, rsi\n" ^"mov r11, [rdi]\n"
      ^ "MAKE_PAIR(r10, r11, r12)\n"  ^ "add rsi, 8\n"
      ^ (Printf.sprintf ("loop create_lst%d\n") create_lst_count) 
      ^ (Printf.sprintf ("Label%d:\n") label_count)
      ^ (Printf.sprintf ("mov qword [rsp+(3+%d)*WORD_SIZE],r10\n") pList_len) 
      ^ (Printf.sprintf ("adjust_stack%d:\n") adjust_stack_count) 
      ^ "sub rsi,8\n"  ^ "add rsi,rsp\n" ^ "mov rdi, rsi\n"
      ^ "mov rsi, rsp\n" 
      ^ (Printf.sprintf ("mov rdx, 24 + (%d+1)*8\n") pList_len)
      ^ "call memmove\n" ^ "mov rsp,rax\n"
      ^ (Printf.sprintf ("mov qword [rsp + 16],%d+1\n") pList_len)
      ^ (Printf.sprintf ("jmp finish%d\n") finish_count)
      ^ (Printf.sprintf ("kill_magic%d:\n") kill_magic_count) ^ "shl rdx,3\n" ^"mov qword [rsp + 24 + rdx], SOB_NIL_ADDRESS\n" 
      ^ (Printf.sprintf ("finish%d:\n") finish_count)
      ;(create_lst_counter := !create_lst_counter+1)
      ;(kill_magic_counter := !kill_magic_counter+1)
      ;(finish_counter := !finish_counter+1)
      ;(adjust_stack_counter := !adjust_stack_counter+1)
      ;(label_counter:= !label_counter+1)






in let res = (scanExp 0 (-1) consts fvars e) in (retUnit2 res);!string;;


end;;

