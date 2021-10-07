
#use "pc.ml";;

open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;


type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2)
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
(* module Reader = struct *)

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

(*Auxiliary parsers for read_sexpr function*)

let concatLists x = match x with | (a,b)-> a@b;;

let whitespace_star = star nt_whitespace;;

let make_spaced nt =
  make_paired whitespace_star whitespace_star nt;;

(*Symbol*)

let symbolCharParser = let nt = disj_list [(range '0' '9');(range 'a' 'z');(range 'A' 'Z'); (one_of "!$^*-_=+<>?/:")] in
                       let nt = pack nt lowercase_ascii in
                       let nt = pack nt (fun x->[x]) in
                       nt;;


let symbolMaker sym = Symbol(sym);;


let symbolParser = let nt = plus symbolCharParser in
                   let nt = pack nt List.flatten in
                   let nt = pack nt list_to_string in
                   let nt = pack nt symbolMaker in
                   let nt = make_spaced nt in
                   nt;;

(*Boolean*)

let makeBool lst = match lst with
                    | [] -> raise X_no_match
                    | car::cdr -> let b = (lowercase_ascii (List.nth lst 1)) in
                                  match b with
                                  |'t'-> Bool(true)
                                  |'f'-> Bool(false)
                                  |_->raise X_no_match;;


let boolParser  = let nt = disj (word_ci "#t") (word_ci "#f") in
                  let nt = make_spaced nt in
                  let nt = pack nt makeBool in
                  nt;;

(*Char*)

let visibleSimpleCharParser = pack (range '!' '~') (fun x -> [x]);;

let namedCharParser = disj_list [word_ci "newline"; word_ci "nul"; word_ci "page"; word_ci "return"; word_ci "space"; word_ci "tab"];;


let makeChar lst = match lst with
                   | [] -> raise X_no_match
                   | car::cdr -> let len = List.length lst in
                                 match len with
                                 | 3 -> Char((List.nth lst 2))
                                 | _ -> let s = String.sub (list_to_string (List.map lowercase_ascii lst)) 2 (len-2) in
                                        match s with
                                        | "nul" -> Char(Char.chr 0)
                                        | "newline" -> Char(Char.chr 10)
                                        | "page" -> Char(Char.chr 12)
                                        | "return" -> Char(Char.chr 13)
                                        | "space" -> Char(Char.chr 32)
                                        | "tab" -> Char(Char.chr 9)
                                        | _-> raise X_no_match;;

let charParser = let nt = (disj namedCharParser visibleSimpleCharParser) in
                 let nt = caten (word "#\\") nt in
                 let nt = pack nt concatLists in
                 let nt = make_spaced nt in
                 let nt = pack nt makeChar in
                 nt;;


(*Number *)

(*Int*)
let naturalMaker =
  let make_nt_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
		      fun ch -> (Char.code ch) - delta) in
    nt in
  let nt = make_nt_digit '0' '9' 0 in
  let nt = plus nt in
  let nt = pack nt (fun digits ->
		    List.fold_left (fun a b -> 10 * a + b) 0 digits) in
  nt;;


let signParser = (disj (char '+') (char '-'));;


let auxIntegerParser = pack (maybe signParser) (fun x-> match x with | Some('+')-> ['+'] |Some('-')-> ['-'] |_->[]);;


let makeInteger tuple = match tuple with
                    | (a,b) -> match a with
                               |['-']-> Number(Int(0-b))
                               |_-> Number(Int(b));;

let integerParser = let nt = (caten auxIntegerParser naturalMaker) in
                    let nt = pack nt makeInteger in
                    nt;;

let dotParser = pack (char '.') (fun x -> [x]);;



let floatParser s = let string = list_to_string s in
                    let sign = if((String.length string) > 1 && String.sub string 0 1 = "-" && String.sub string 1 1 = "0") then (-1.) else 1. in
                    let nt = caten integerParser dotParser in
                    let nt = pack nt (fun (x,y)-> match x with| Number(Int(num))->String.concat "" [(string_of_int num);"."]| _->raise X_no_match) in
                    let nt = caten nt (plus (range '0' '9')) in
                    let nt = pack nt (fun (a,b)-> String.concat "" [a;(list_to_string b)]) in
                    let nt = pack nt float_of_string in
                    let nt = pack nt (fun x-> if ( x < 0.) then x else x*.sign) in
                    let nt = pack nt (fun x-> Number(Float(x))) in
                    nt s;;

let scientificNoParser = let nt = disj floatParser integerParser in
                         let nt = caten nt (char_ci 'e') in
                         let nt = pack nt (fun(x,y) -> match x with | Number(Int(x)) -> float_of_int x
                                                                    | Number(Float(x)) -> x
                                                                    | _-> raise X_no_match) in
                         let nt = caten nt integerParser in
                         let nt = pack nt (fun(x,y) -> match y with | Number(Int(y)) -> (x, float_of_int y)
                                                                    | Number(Float(y)) -> (x,y)
                                                                    | _-> raise X_no_match) in
                        let nt = pack nt (fun(x,y) -> x *. (10. ** y)) in
                        let nt = pack nt (fun(x) -> Number(Float(x))) in
                        nt;;

let auxRadixParser = let nt = disj (range '0' '9') (range 'a' 'z') in
                     let nt = disj nt (range 'A' 'Z') in
                     let nt = disj nt (char '.') in
                     let nt = pack nt lowercase_ascii in
                     nt;;


let make_num_list char = let ch = int_of_char char in
                                  if ch >= 48 && ch <= 57 then ch-48
                                  else if ch = 46 then ch else ch-87;;

let baseIntParser list base sign =    let res =
		                                  (List.fold_left (fun a b -> base * a + b) 0 list) in
                                       match sign with |'-' -> Number(Int ((-1*res)))
                                                       |_-> Number(Int(res));;


let rec recCalc list acc count base = if List.length list = count then acc
                                      else recCalc list (acc +. (List.nth list count)*.(base ** (-1. *. (float_of_int (count+1))))) (count+1) base ;;

let baseFloatParser list base sign = let dotIndex = String.index list '.' in
                                     let l1 = String.sub list 0 dotIndex in
                                     let l2 = String.sub list (dotIndex+1) ((String.length list)-dotIndex-1) in
                                     let l1 = string_to_list l1 in
                                     let left = baseIntParser (List.map make_num_list l1) base sign in
                                     let left = match left with |Number(Int(res)) -> float_of_int res
                                                                |_ -> 0. in
                                     let l2 = List.map make_num_list (string_to_list l2) in
                                     let l2 = List.map float_of_int l2 in
                                     let right = recCalc l2 0. 0 (float_of_int base) in
                                     let right = if left < 0. then right *. (-1.) else right in
                                     let res = left +. right in
                                     let res = if right > 0. && sign = '-' && left = 0. then res *.(-1.) else res in
                                     let res = Number(Float(res)) in
                                     res;;


let radixParser s = let nt = caten (char '#') naturalMaker in
                    let nt = pack nt (fun(x,y) -> if (y >= 2 && y <= 36) then y else raise X_no_match) in
                    let r =  ((fun(x,y) -> x) (nt s)) in  (*saving the radix*)
                    let nt = caten nt (char_ci 'r') in

                    let checkChar c = let ch = int_of_char c in
                                      if ch >= 48 && ch <= 57 && ch < r+48 then true
                                      else if ch >= 97 && ch <= 122 && ch <= r+86 then true
                                      else if ch = 46 then true else false  in

                    let nt = pack nt (fun(x,y) -> x) in   (*taking off the r_char*)
                    let nt = caten nt auxIntegerParser in (*putting sign *)
                    let sign = ((fun(x,y) -> match x with | (_,['-']) -> '-'
                                                          | _-> '+')(nt s)) in
                    let nt = pack nt (fun(x,y) -> y) in  (*removing thr r_actual base*)
                    let nt = caten nt (plus (guard auxRadixParser checkChar)) in
                    let nt = pack nt (fun(x,y) -> y) in
                    let nt = pack nt (fun (e) -> if(List.mem '.' e) then (baseFloatParser (list_to_string e) r sign)
                                                 else (baseIntParser (List.map make_num_list e) r sign)) in
                    nt s;;


let numberParser = let nt = disj scientificNoParser floatParser in
                   let nt = disj nt integerParser in
                   let nt = not_followed_by nt symbolCharParser in
                   let nt = disj nt radixParser in
                   let nt = make_spaced nt in
                   nt ;;


(*String*)

let stringLiteralCharParser = let nt = one_of "\"\\" in
                              let nt = diff nt_any nt in
                              let nt = pack nt (fun x-> [x]) in
                              nt;;

let slashParser = word "\"";;

let stringMetaCharParser = let nt_temp = char '\\' in
                           let nt = disj_list [char '\\'; char '\"' ;char_ci 't';char_ci 'f'; char_ci 'n'; char_ci 'r'] in
                           let nt = caten nt_temp nt in
                           let nt = pack nt (fun (a,b)-> match b with|
                                                         '\\'->['\\']| '"'-> ['\"']| ('t'|'T') -> ['\t']| ('f'|'F') -> [Char.chr 12]|
                                                         ('n'|'N') -> ['\n']| ('r'|'R') -> ['\r']| _ -> raise X_no_match) in
                           nt;;

let stringCharParser = disj stringLiteralCharParser stringMetaCharParser;;

let makeString s = String(s);;


let stringParser = let nt = star stringCharParser in
                   let nt = pack nt List.flatten in
                   let nt = make_paired slashParser slashParser nt in
                   let nt = make_spaced nt in
                   let nt = pack nt list_to_string in
                   let nt = pack nt makeString in
                   nt;;


(*Recursive lists *)

let rec list_to_pair_list l = match l with
                                |[]->Nil
                                |car::cdr-> match car with | Symbol("NilFlag") -> (list_to_pair_list cdr)
                                                           | _-> Pair(car, (list_to_pair_list cdr));;


let rec dotted_list_to_pair_list (sExpPlus,lastSExp) = match sExpPlus with
                                |[] -> lastSExp
                                |car::cdr-> match car with | Symbol("NilFlag") -> (dotted_list_to_pair_list (cdr,lastSExp))
                                                           | _-> Pair(car, (dotted_list_to_pair_list (cdr,lastSExp)));;


let rec sexpParser s =
let makeSexpParser = disj_list [boolParser; charParser; numberParser; stringParser; symbolParser;listParser;dottedListParser
                                ;quatedParser;qquotedParser;unquotedSlicingParser;unquotedParser;tagExpParser;tagParser
                                ;lineCommentParser;commentParser]
                     in makeSexpParser s

and listParser s = let nt = star sexpParser in
                   let nt = make_spaced nt in
                   let nt = make_paired (char '(') (char ')') nt in
                   let nt = make_spaced nt in
                   let nt = pack nt list_to_pair_list in
                   nt s

and dottedListParser s = let nt = plus sexpParser in
                         let nt = caten nt (char '.') in
                         let nt = pack nt (fun (first,second)-> first) in

                         let nt2 = star (disj lineCommentParser commentParser) in
                         let nt2 = make_paired nt2 nt2 sexpParser in

                         let nt = caten nt nt2 in
                         let nt = make_paired (char '(') (char ')') nt in
                         let nt = make_spaced nt in
                         let nt = pack nt dotted_list_to_pair_list in
                         nt s

and quatedParser s = let nt = caten (char '\'') sexpParser in
                     let nt = pack nt (fun(x,y) -> Pair(Symbol("quote"), Pair(y,Nil))) in
                     nt s

and qquotedParser s = let nt = caten (char '`') sexpParser in
                      let nt = pack nt (fun(x,y) -> Pair(Symbol("quasiquote"), Pair(y,Nil))) in
                      (make_spaced nt) s

and unquotedSlicingParser s = let nt = caten (word ",@") sexpParser in
                              let nt = pack nt (fun(x,y) -> Pair(Symbol("unquote-splicing"), Pair(y,Nil))) in
                              (* nt s *)
                              (make_spaced nt) s

and unquotedParser s = let nt = caten (char ',') sexpParser in
                       let nt = pack nt (fun(x,y) -> Pair(Symbol("unquote"), Pair(y,Nil))) in
                       (make_spaced nt) s

and tagExpParser s = let nt = caten (char '=') sexpParser in
                     let nt = maybe nt in
                     let nt = caten tagParser nt in
                     let nt = pack nt (fun(x,y) -> match y with
                                                  |None -> (match x with |Symbol(z) -> TagRef(z)
                                                          |_ -> raise X_no_match )
                                                  |Some(a,b) -> TaggedSexpr((match x with |Symbol(t) -> t|_ -> raise X_no_match), b)) in
                     nt s

and tagParser s = let nt = make_paired (char '{') (char '}') symbolParser in
                  let nt = caten (char '#') nt in
                  let nt = pack nt (fun(x,y) -> y) in
                  (make_spaced nt) s

and lineCommentParser s = let nt = char ';' in
                          let nt = caten nt (star(diff nt_any (char '\n'))) in
                          let nt = caten nt (disj nt_end_of_input (word "\n")) in
                          let nt = make_spaced nt in
                          let nt = pack nt (fun(x) -> Symbol("NilFlag"))  in
                          nt s

and commentParser s = let rec auxCommentParser s = let e  = make_spaced(make_paired (word "#;") sexpParser auxCommentParser)  in
                      let nt = caten e e in
                      let nt = pack nt (fun(x,y) -> x@y) in
                      let nt = disj nt e in
                      let nt = disj nt nt_epsilon in
                      nt s in
                      let nt = make_spaced(make_paired (word "#;") sexpParser auxCommentParser)  in
                      let nt = pack nt (fun(x) -> Symbol("NilFlag"))  in
                      nt s;;




(* those functions were up.. *)
let rec auxForReadSexprs sexpr = match sexpr with |Pair(car, Nil) -> [car]
                                                  |Pair(car,cdr) -> [car]@(auxForReadSexprs cdr)
                                                  |Nil->[]
                                                  |_ -> raise X_no_match ;;


let rec taggedCheck lst sExp = match sExp with
                           |TaggedSexpr (name,rest)-> if (List.mem name lst)
                                                     then raise X_this_should_not_happen
                                                     else taggedCheck (lst@[name]) rest
                           |Pair(a,Nil)-> (taggedCheck lst a)
                           |Pair(a,b)-> (let res1 = (taggedCheck lst a) in
                                          taggedCheck res1 b)
                           |_-> lst;;

let nilRemove lst = let res = List.filter (fun x-> x<>Symbol("NilFlag")) lst in res;;


let read_sexpr string =
  let nt = star (disj lineCommentParser commentParser) in
  let nt = make_paired nt nt sexpParser in
  let l = string_to_list string in
  let (res,rest) = nt l in
  match rest with
  | [] -> (let res2 = (taggedCheck [] res) in match res2 with| _-> res)
  |_-> raise X_no_match;;



let read_sexprs string = let nt = star sexpParser in
                         let s = string_to_list string in
                         let sexpList = nt s in
                         let sexpList = match sexpList with|(a,b)->a in
                         let res = List.map (taggedCheck []) sexpList in
                         match res with|_-> nilRemove sexpList;;


end;; (* struct Reader *)
