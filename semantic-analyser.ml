#use "tag-parser.ml";;
open Tag_Parser;;

type var =
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;
exception X_this_should_not_happen;;
exception X_this_should_not_happen2;;
exception Test;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e =
  let rec to_expr' varList majorIndex expr = match expr with
      | Const(s) -> Const'(s)
      | Var(varName) -> (checkVarType varName varList majorIndex)
      | If(test,th,el) -> If'((to_expr' varList majorIndex test), (to_expr' varList majorIndex th), (to_expr' varList majorIndex el))
      | Seq(exprList) -> Seq'((List.map (to_expr' varList majorIndex) exprList))
      | Set(exp,value)-> Set'((to_expr' varList majorIndex exp), (to_expr' varList majorIndex value))
      | Def(exp,value) -> Def'((to_expr' varList majorIndex exp), (to_expr' varList majorIndex value))
      | Or(exprList) -> Or'((List.map (to_expr' varList majorIndex) exprList))
      | LambdaSimple(paramList,body) -> LambdaSimple'(paramList,(to_expr' (paramList::varList) majorIndex body))
      | LambdaOpt(paramList,optList,body) -> LambdaOpt'(paramList,optList,(to_expr' ((paramList@[optList])::varList) majorIndex body))
      | Applic(expr,exprList)-> Applic'((to_expr' varList majorIndex expr), (List.map (to_expr' varList majorIndex) exprList))


      and checkVarType varName varList majorIndex =
          let paramList = List.nth_opt varList 0 in (match paramList with
            |None -> Var'(VarFree(varName))
            |Some(list)-> if (List.mem varName list)
                          then (if(majorIndex = 0)
                                then Var'(VarParam(varName,(getVarLocation varName 0 list)))
                                else Var'(VarBound(varName,majorIndex-1,(getVarLocation varName 0 list))))
                          else (match varList with|[lastList] -> Var'(VarFree(varName))
                                                  |head::rest-> (checkVarType varName rest (majorIndex+1))
                                                  |_->raise X_this_should_not_happen))

      and getVarLocation varName index list =
          if((List.nth list index) = varName) then index else (getVarLocation varName (index+1) list)

      in (to_expr' [] 0 e)
      ;;




let annotate_tail_calls e =
  let rec annotate_tail_applics in_tp e = (match e with
    | Const'(s) -> e
    | Var'(x) -> e
    | If'(test,th,el) -> If'((annotate_tail_applics false test),(annotate_tail_applics in_tp th),(annotate_tail_applics in_tp el))
    | Seq'(exprList) -> let (firstsList,last) = (splitList exprList []) in Seq'((List.map (annotate_tail_applics false) firstsList)@[(annotate_tail_applics in_tp last)])
    | Set'(exp,value) -> Set'((annotate_tail_applics false exp),(annotate_tail_applics false value))
    | Def'(exp,value) -> Def'((annotate_tail_applics false exp),(annotate_tail_applics false value))
    | Or'(exprList) -> let (firstsList,last) = (splitList exprList []) in Or'((List.map (annotate_tail_applics false) firstsList)@[(annotate_tail_applics in_tp last)])
    | LambdaSimple'(paramList,body) -> LambdaSimple'(paramList,(annotate_tail_applics true body))
    | LambdaOpt'(paramList,optList,body) -> LambdaOpt'(paramList,optList,(annotate_tail_applics true body))
    | Applic'(op,rands)-> if (in_tp = true) then ApplicTP'((annotate_tail_applics false op),(List.map (annotate_tail_applics false) rands))
                                            else Applic'((annotate_tail_applics false op),(List.map (annotate_tail_applics in_tp) rands))
    | _->raise X_this_should_not_happen)

  and splitList list firsts = (match list with
        |[last] -> (firsts,last)
        |head::rest -> (splitList rest (firsts@[head]))
        |_->raise X_this_should_not_happen)



  in (annotate_tail_applics false e);;
;;

let mergeTupples tup1 tup2 = match tup1,tup2 with
                              |(a,b),(c,d) -> (a@c,b@d);;

let box_set e =
  let rec box_set_main exp = (match exp with
    | Const'(x) -> exp
    | Var'(x) -> exp
    | BoxGet'(x) -> exp
    | Set'(Var'(VarParam(_,_)), Box'(VarParam(_,_))) -> exp
    | BoxSet'(x,expr) -> BoxSet'(x, (box_set_main expr))
    | If'(t, th, el) -> If'((box_set_main t), (box_set_main th) , (box_set_main el))
    | Seq'(lst) -> Seq'(List.map box_set_main lst)
    | Set'(x,value) -> Set'(x, (box_set_main value))
    | Def'(x,value) -> Def'(x, (box_set_main value))
    | Or'(lst) -> Or'(List.map box_set_main lst)
    | LambdaSimple'(p,body) -> let newBody = box_set_aux p body in
                               LambdaSimple'(p, box_set_main newBody)
    | LambdaOpt'(pList,optList,body) -> let newBody = box_set_aux (pList@[optList]) body in
                               LambdaOpt'(pList,optList, box_set_main newBody)
    | Applic'(op,args) -> Applic'(box_set_main op, (List.map box_set_main args))
    | ApplicTP'(op,args) -> ApplicTP'(box_set_main op, (List.map box_set_main args))
    |_ -> raise X_this_should_not_happen)

  and box_per_param body count indexArr param =
    (match body with
    | Const'(x) -> ([],[])  (* left = setArr , right = getArr*)
    | Var'(x) -> (match x with
                    |VarFree(_) -> ([],[])
                    |VarParam(name,_) -> if(name = param) then ([],[indexArr]) else ([],[])
                    |VarBound(name,_,_) -> if(name = param) then ([],[indexArr]) else ([],[]))

    | BoxGet'(x) -> ([],[])
    | BoxSet'(x,expr) -> (box_per_param expr count indexArr param)
    | If'(t, th, el) -> (box_per_param (Seq'([t;th;el])) count indexArr param)

    | Seq'(lst) -> let oldCount = ref !count in
                   let res =  (List.map (fun element -> (match element with
                                                      | LambdaSimple'(_,_)->
                                                          (let res = (box_per_param element count indexArr param) in
                                                          (count := !oldCount + 1) ; oldCount := !count ; res)
                                                      | LambdaOpt'(_,_,_)->
                                                          (let res = (box_per_param element count indexArr param) in
                                                          (count := !oldCount + 1) ; res)
                                                      | _-> (box_per_param element count indexArr param)))
                        lst) in
                          let res = (List.fold_left mergeTupples ([],[]) res) in res


    | Set'(var,value) -> let res = (match var with
                                      |Var'(VarFree(_)) -> ([],[])
                                      |Var'(VarParam(varName,_)) ->
                                            (if(varName = param) then ([indexArr],[]) else ([],[]))
                                      |Var'(VarBound(varName,_,_)) ->
                                            (if(varName = param) then ([indexArr],[]) else ([],[]))
                                      |_-> raise X_this_should_not_happen2) in
                                      (mergeTupples res (box_per_param value count indexArr param))

    | Def'(x,value) -> (box_per_param value count indexArr param)
    | Or'(lst) -> (box_per_param (Seq'(lst)) count indexArr param)

    | LambdaSimple'(p,body) -> if(List.mem param p) then ([],[])
                               else (box_per_param body count (indexArr@[!count]) param)


    | LambdaOpt'(pList,optList,body) -> if(List.mem param (pList@[optList])) then ([],[])
                                        else (box_per_param body count (indexArr@[!count]) param)

    | Applic'(op,args) -> (box_per_param (Seq'([op]@args)) count indexArr param)
    | ApplicTP'(op,args) -> (box_per_param (Seq'([op]@args)) count indexArr param)
    |_ -> raise X_this_should_not_happen)

  and checkBoxAux e1 e2 = if ((e1=[] && e2<>[]) || (e2=[] && e1<>[]))  then true else
                          if (e1 = e2) then false
                          else if ((List.nth e1 0) = (List.nth e2 0)) then false else true

  and checkBox tupple = (match tupple with
                          |(getList , setList) ->
                            let res = (List.map (fun e1 ->
                                        (List.map (fun e2 -> checkBoxAux e1 e2) setList)) getList) in
                            (List.mem true (List.flatten res)))

  and modifyBody body param = match body with
        | Const'(x) -> body
        | Var'(x) -> (match x with
                    |VarFree(_) -> body
                    |VarParam(name,_) -> if(name = param) then (BoxGet'(x)) else body
                    |VarBound(name,_,_) -> if(name = param) then (BoxGet'(x)) else body)
        | BoxGet'(x) -> body
        | BoxSet'(x,expr) -> BoxSet'(x, modifyBody expr param)
        | If'(t, th, el) -> If'(modifyBody t param, modifyBody th param, modifyBody el param)
        | Seq'(lst) -> Seq'(List.map (fun e -> modifyBody e param) lst)
        | Set'(var,value) -> (match var with
                              |Var'(v) -> (match v with
                                  |VarParam(varName,_)->
                                    (if(varName = param)
                                    then (BoxSet'(v, (modifyBody value param)))
                                    else (Set'(var, (modifyBody value param))))
                                  |VarBound(varName,_,_)->
                                        (if(varName = param)
                                        then (BoxSet'(v, (modifyBody value param)))
                                        else (Set'(var, (modifyBody value param))))
                                  |VarFree(varName) -> Set'(var, (modifyBody value param)))
                              |_ -> raise X_this_should_not_happen)

        | Def'(x,value) -> Def'(x, (modifyBody value param))
        | Or'(lst) -> Or'(List.map (fun e -> modifyBody e param) lst)
        | LambdaSimple'(pList,lBody) -> if(List.mem param pList) then body
                                        else LambdaSimple'(pList, (modifyBody lBody param))
        | LambdaOpt'(pList,optList,lBody) -> if(List.mem param (pList@[optList])) then body
                                            else LambdaOpt'(pList, optList, (modifyBody lBody param))

        | Applic'(op,args) -> Applic'((modifyBody op param),(List.map (fun e -> modifyBody e param) args))
        | ApplicTP'(op,args) -> ApplicTP'((modifyBody op param),(List.map (fun e -> modifyBody e param) args))
        |_-> raise X_this_should_not_happen


  and callingModify body pList boolList = let body = (match pList with
                                              |[] -> body
                                              |car::cdr -> if(List.nth boolList 0)
                                                           then (callingModify (modifyBody body car) cdr (List.tl boolList))
                                                           else (callingModify body cdr (List.tl boolList))) in body


  and addExprBox body pList boolList index lst =
                                        let lst = (match pList with
                                              |[] -> lst
                                              |car::cdr -> if(List.nth boolList 0)
                                                           then (lst@[Set'(Var'(VarParam(car, index)), Box'(VarParam(car, index)))])
                                                           else lst) in
                                              if((List.length pList) = 0)
                                              then (if ((List.length lst) > 0) then Seq'(lst@[body]) else body)
                                              else (addExprBox body (List.tl pList) (List.tl boolList) (index +1) lst)


  and box_set_aux pList body = let count = ref 1 in
                               let tupplesList = (List.map (box_per_param body count []) pList) in
                               let boolList = (List.map checkBox tupplesList) in
                               let modifiedBody = callingModify body pList boolList in
                               let newBody = addExprBox modifiedBody pList boolList 0 [] in newBody

  in box_set_main e;;



let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)