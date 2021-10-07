#use "reader.ml";;
open Reader;;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_this_should_not_happen;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)
module Tag_Parser : TAG_PARSER = struct
(* module Tag_Parser = struct *)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)


let rec list_to_pair_list l = (match l with
                                |[]->Nil
                                |car::cdr->Pair(car, (list_to_pair_list cdr)));;

let rec list_to_improper_pair_list l = (match l with
                                |[last]->last
                                |car::cdr->Pair(car, (list_to_improper_pair_list cdr))
                                |[]->Nil);;
                                                          
let rec auxCheckProperList p = (match p with
                                | Nil -> true
                                | Pair(x,y) -> auxCheckProperList y
                                | _-> false);;

let rec checkArgDuplicates argl lst = (match argl with
                                      |Pair(Symbol(argName), rest)-> if (List.mem argName lst) then true else (checkArgDuplicates rest (lst@[argName]))
                                      |_->false);;

let checkProperList lst = (match lst with
                          | Nil -> true
                          | Pair(_,_) -> auxCheckProperList lst
                          | _ -> false);;

let rec properToList pList = (match pList with
                                |Nil -> []
                                |Pair(car,cdr) -> [car]@(properToList cdr)
                                |_ -> raise X_syntax_error);;

let sListToString sList = List.map (fun(x) -> (match x with |Symbol(y) -> y |_ -> raise X_syntax_error)) sList;;



let rec improperToListTuple lst args = (match lst with
                                           |Symbol(a) -> (args, a)
                                           |Pair(Symbol(a),Symbol(b))-> (args@[a],b)
                                           |Pair(Symbol(a),Pair(Symbol(x),y))-> improperToListTuple y (args@[a;x])
                                           |_->raise X_syntax_error);;

let rec quasiExpand sexpr = (match sexpr with
                            |Pair(Symbol "unquote", Pair(e, Nil))-> e
                            |Pair(Symbol "unquote-splicing", Pair(e, Nil))-> raise X_syntax_error
                            |Nil-> Pair(Symbol "quote",Pair(Nil,Nil))
                            |Symbol(x)-> Pair(Symbol "quote",Pair(Symbol(x),Nil))
                            |Pair(a,b)-> (match a,b with
                              |Pair(Symbol "unquote-splicing", Pair(e, Nil)),_ -> Pair(Symbol("append"), Pair(e, Pair((quasiExpand b), Nil)))
                              |_,Pair(Symbol "unquote-splicing", Pair(e, Nil))-> Pair(Symbol("cons"), Pair((quasiExpand a), Pair(e, Nil)))
                              |_,_-> Pair(Symbol("cons"), Pair((quasiExpand a),Pair((quasiExpand b), Nil))))
                            |_->sexpr);;

let rec andExpand sexpr = (match sexpr with
                          |Pair(Symbol "and",Nil)-> Bool(true)
                          |Pair(Symbol "and", Pair(e, Nil))-> andExpand e
                          |Pair(Symbol "and", Pair(a,b))-> Pair(Symbol("if"),(Pair((andExpand a),Pair(andExpand (Pair(Symbol("and"),b)),Pair(Bool(false),Nil)))))
                          |_ -> sexpr);;

(* bindings = Pair(Pair(Symbol "value", Pair(Pair (Symbol "h?", Pair (Symbol "x", Nil)),Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair (Symbol "p", Pair (Symbol "q", Nil)),Nil))), Nil)), Nil))
rib = Pair(Symbol "value", Pair(Pair (Symbol "h?", Pair (Symbol "x", Nil)),Nil))
ribs = Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair (Symbol "p", Pair (Symbol "q", Nil)),Nil))), Nil)), Nil) *)

let rec expandLet argList body = (match argList with
                                 
                                 |Nil->Pair(Pair(Symbol("lambda"),Pair(Nil, body)),Nil)

                                 |Pair(rib,ribs)-> let (args,params) = auxLet argList [] [] in 

                                
                                  Pair(Pair(Symbol("lambda"),Pair(args, body)),params)
                                 |_-> raise X_this_should_not_happen)
                                  
                                 
and auxLet lst args params = (match lst with
                                 |Nil-> ((list_to_pair_list args),(list_to_pair_list params))
                                 |Pair(rib,ribs)-> (match rib with|Pair(arg, Pair(param, Nil))->auxLet ribs (args@[arg]) (params@[param]) |_->raise X_this_should_not_happen)
                                 |_->raise X_syntax_error);;




let expandMIT argList body = (match body with 
                             |Nil->raise X_syntax_error
                             |_-> Pair(Symbol("lambda"), Pair(argList, body)));; 


let rec expandLetStar bindings body = (match bindings with
                                  |Nil->Pair(Symbol("let"), Pair(Nil, body))
                                  |Pair(Pair(var, Pair(exp, Nil)), Nil) ->  Pair(Symbol "let", Pair(Pair(Pair(var, Pair(exp, Nil)), Nil), body))
                                  |Pair(rib,ribs) -> Pair(Symbol "let", Pair(Pair(rib,Nil),Pair((expandLetStar ribs body),Nil)))
                                  |_->raise X_this_should_not_happen);;


let rec expandLetrec bindings body = (match bindings with
                                 |Nil-> Pair(Symbol("let"), Pair(Nil, body))
                                 |Pair(rib,ribs) -> createLetrec bindings body
                                 |_->raise X_this_should_not_happen)

and createLetrec bindings body = let listOfBindingPairs = (properToList bindings) in
                                 let listOfBindingTuples = List.map (fun x-> match x with|Pair(Symbol(arg), Pair (exp, Nil))->(arg,exp) |_->raise X_this_should_not_happen) listOfBindingPairs in
                                 let what = Pair(Symbol("quote"),Pair(Symbol("whatever"),Nil)) in
                                 let whateverBindingList = List.map (fun (x,y)-> Pair(Symbol(x),Pair(what,Nil))) listOfBindingTuples in
                                 let whateverBindingList = list_to_pair_list whateverBindingList in
                                 let setList = List.map (fun (arg,exp)-> Pair(Symbol "set!", Pair(Symbol(arg), Pair(exp,Nil)))) listOfBindingTuples in
                                 let newBody = (list_to_improper_pair_list (setList@[body])) in
                                 let newLetrec = Pair(Symbol "let", Pair(whateverBindingList,newBody)) in newLetrec;;



let rec expandCond rib ribs = (match rib with
                          |Pair(Symbol "else", elseClause) -> Pair(Symbol("begin"),elseClause)
                          |Pair(exprk, Pair(Symbol "=>", Pair(exprf, Nil)))->

                           (match ribs with 
                           |Nil ->
                              let bindings = Pair(Pair(Symbol "value", Pair(exprk,Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(exprf,Nil))), Nil)), Nil)) in
                              let body = Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))),Nil) in
                              let res = Pair(Symbol("let"), Pair(bindings, body)) in res
                           |Pair(a,b) -> 
                              let bindings = Pair(Pair(Symbol "value", Pair(exprk,Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(exprf,Nil))), Nil)),
                                              Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair((expandCond a b),Nil) )), Nil)), Nil))) in
                              let body = Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil) in
                              let res = Pair(Symbol("let"), Pair(bindings, body)) in res
                           |_->raise X_this_should_not_happen)
  
                           |Pair(test, body) -> (match ribs with 
                                                   |Nil -> Pair(Symbol "if", Pair(test, Pair(Pair(Symbol "begin", body),Nil)))
                                                   |Pair(a,b) -> Pair(Symbol "if", Pair(test, Pair(Pair(Symbol "begin", body),Pair((expandCond a b),Nil))))
                                                   |_->raise X_this_should_not_happen)
                           |_->raise X_this_should_not_happen);;
                                                                 


let rec tag_parse = function
        | Nil-> raise X_syntax_error
        | Bool(e) -> Const(Sexpr(Bool(e)))
        | Number(e) -> Const(Sexpr(Number(e))) 
        | Char(e) -> Const(Sexpr(Char(e)))
        | String(e) -> Const(Sexpr(String(e)))
        | Pair(Symbol("quote"), Pair(e, Nil)) -> Const(Sexpr(e))
        | TaggedSexpr(a,b) -> (match b with
                              | Pair(Symbol("quote"), Pair(e, Nil)) -> Const(Sexpr(TaggedSexpr(a,e)))
                              | _ -> Const(Sexpr(TaggedSexpr(a,b))))
        | TagRef(e) -> Const(Sexpr(TagRef(e)))

              
        | Pair(Symbol("if"),Pair(test, Pair(dit,Nil))) -> If(tag_parse test, tag_parse dit, Const(Void))
        | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)
        | Symbol(e) -> (if(List.mem e reserved_word_list) then raise X_syntax_error else Var(e))     

                                   
          

        | Pair(Symbol("lambda"), Pair(e, body)) -> if (checkArgDuplicates e []) then raise X_syntax_error else createBody e body

        | Pair(Symbol "or", Nil) -> tag_parse (Bool(false))
        | Pair(Symbol "or", Pair(e,Nil)) -> tag_parse e
        | Pair(Symbol "or", Pair(a,b)) -> let lst = properToList (Pair(a,b)) in  
                                         let lst = List.map tag_parse lst in
                                         Or(lst)

        | Pair(Symbol "define", Pair(Symbol(name), Pair(expr,Nil)))-> Def((tag_parse (Symbol(name))), (tag_parse expr)) 
        | Pair(Symbol "define", Pair(Pair(Symbol(name),argl),body))-> let res = (expandMIT argl body) in 
                                                                     Def((tag_parse (Symbol(name))), (tag_parse res)) 
        

        | Pair(Symbol "set!", Pair(Symbol(name), Pair(expr,Nil)))-> Set((tag_parse (Symbol(name))), (tag_parse expr)) 
         
        | Pair(Symbol("begin"),Nil)-> Const(Void)
        | Pair(Symbol("begin"),body)-> let newbody = (bodyParseToSeq body) in newbody

        | Pair(Symbol "quasiquote",Pair(e,Nil)) -> let res = quasiExpand e in tag_parse res
        | Pair(Symbol "and",e)-> let res = andExpand (Pair(Symbol "and",e)) in tag_parse res 
        (* | Pair(Symbol("let"), Pair(Nil, body)) -> let res = (expandLet Nil  body) in tag_parse res *)
        (* | Pair(Symbol("let"), Pair(bindings, Pair(body, Nil))) -> let res = (expandLet bindings body) in tag_parse res *)
        | Pair(Symbol("let"), Pair(bindings, body)) -> let res = (expandLet bindings body) in tag_parse res

        (* | Pair(Symbol "let*", Pair(Nil, body))-> let res = (expandLet bindings body) in tag_parse res *)
        | Pair(Symbol "let*", Pair(bindings, body))-> let res = expandLetStar bindings body in tag_parse res
         


        | Pair(Symbol "letrec",Pair(bindings,body)) -> let res = expandLetrec bindings body in tag_parse res

        | Pair(Symbol "cond", Pair(rib,ribs)) -> let res = (expandCond rib ribs) in tag_parse res
          
        | Pair(op, e) ->  (match e with
                         |Nil -> Applic(tag_parse op,[])
                         |Pair(a,b)->     Applic(tag_parse op, 
                                          let lst = properToList (Pair(a,b)) in 
                                          let lst = List.map tag_parse lst in lst)
                         |_->raise X_this_should_not_happen)
                                          
        and bodyParseToSeq body = (match body with
                                    
                                    |Pair(e,Nil) -> (tag_parse e)
                                    |Pair(a,b) -> if(checkProperList body) then Seq(List.map tag_parse (properToList body)) else raise X_syntax_error
                                    |_->raise X_syntax_error)


        and createBody e body =  let newbody = (bodyParseToSeq body) in  
                                    (match e with
                                    |Nil -> LambdaSimple([],newbody)
                                    |Pair(arg,args) -> if (checkProperList e)
                                              then LambdaSimple(sListToString (properToList e), newbody)
                                              else let (args,vs) = (improperToListTuple e []) in
                                                  LambdaOpt(args,vs,newbody)
                                    |Symbol(vs) -> LambdaOpt([],vs,newbody)
                                    |_->raise X_this_should_not_happen);;


let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse sexpr;;



end;; (* struct Tag_Parser *)
