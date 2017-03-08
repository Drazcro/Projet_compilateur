(* Typechecking of source programs *)

open Lang
open Analyses

(* Environments *)

type environment = 
    {localvar: (vname * tp) list; 
     globalvar: (vname * tp) list; 
     returntp: tp;
     funbind: fundecl list}


(* TODO: put your definitions here *)
let tp_prog (Prog (gvds, fdfs)) =
  Prog([],
       [Fundefn (Fundecl (BoolT, "even", [Vardecl (IntT, "n")]), [], Skip)])
;;

let exp1 = BinOp (0, BCompar BCeq , VarE (0, Var (Local , "n")),
BinOp (0, BArith BAadd , VarE (0, Var (Local , "k")),
Const (0, IntV 1)));;

let exp5 = BinOp (0, BCompar BCeq , VarE (0, Var (Local , "n")),
BinOp (0, BArith BAadd , Const (0, BoolV true),
Const (0, IntV 1)));;

let exp6 = BinOp (0, BCompar BCeq , Const(0, BoolV true),
BinOp (0, BArith BAadd , VarE (0, Var (Local , "k")),
Const (0, IntV 1)));;

let exp7 = CallE (0, "f", [Const (0, IntV 3); Const (0, BoolV true )]);;

let exp8 = BinOp (0, BCompar BCeq , Const(0, BoolV true),
BinOp (0, BArith BAadd , VarE (0, Var (Local , "k")),
CallE (0, "f", [Const (0, IntV 3); Const (0, BoolV true )])));;

let exp9 = BinOp (0, BCompar BCeq , Const(0, BoolV true),
CallE (0, "f", [Const (0, IntV 3); Const (0, BoolV true )]));;

let exp10 = BinOp (0, BArith BAadd , VarE (0, Var (Local , "k")),
CallE (0, "f", [Const (0, IntV 3); Const (0, BoolV true )]));;

let exp11 = BinOp (0, BCompar BCeq , VarE (0, Var (Local , "n")),
BinOp (0, BArith BAadd , VarE (0, Var (Local , "k")),
CallE (0, "f", [Const (0, IntV 3); Const (0, BoolV true )])));;

let env1 = {localvar = [("k", IntT ); ("n", IntT )]; globalvar = [];
returntp = VoidT; funbind = [Fundecl(IntT , "f", [Vardecl(IntT , "n"); Vardecl(BoolT , "b")])]};;

(* Exception pour les variables n'existant pas *)
exception VarNotDefined;;

(* Exception pour les erreurs d'évaluation d'expressions *)
exception BadType;;

(* Exception pour les erreurs d'évaluation d'expressions *)
exception BadCallType;;

(* Exception pour les erreurs d'attribuation de variables pour les appels de fonctions *)
exception FunNotDefined;;

(* Récupère la variable dans le tableau *)
let rec getTypeAux = function
((vname, tp)::r, varName) -> if (vname = varName) then tp else getTypeAux(r, varName)
|([], _) -> raise VarNotDefined;;

(*Récupère le type d'une variable dans l'environnement à partir d'un environnement et du nom d'une variable *)
let getTypeVar = fun env v -> match v with 
(Var(Local, varName)) -> getTypeAux(env.localvar, varName)
|(Var(Global, varName)) -> getTypeAux(env.globalvar, varName);;

(* Récupère le type d'expression d'une constante *)
let getTypeCons = function
(IntV(_))-> IntT
|(BoolV(_)) -> BoolT;;

(* Récupère le type d'expression d'une opération binaire *)
let getTypeBinOp = function
(BArith _) -> IntT
|(BCompar _) -> BoolT
|(BLogic _) -> BoolT;;

(* Récupère la déclaration de fonction dans l'environnement*)
let rec getFundecl = function
(_, []) -> raise FunNotDefined
|(name, Fundecl(eType , fName, varList)::r) -> if(name = fName) then Fundecl(eType , fName, varList) else getFundecl(name, r);;
						
 
(* vérifie si les variables de la déclaration de fonction et celles de l'appel de la fonctions sont compatibles*)
let rec compareVarList = function
([], [], _) -> true
| ([], _, _) -> false
| (_, [], _) -> false
| (ct::cr, Vardecl(eVType , _)::fr, env) ->if(ct = eVType) then compareVarList(cr, fr, env) else false;;
 
(* Vérifie que deux expressions sont bien du même type et qu'elles sont compatibles avec l'opération binaire*)
let compareBOExp = function 
(t1, t2, IntT) -> t1 = t2 & t1 = IntT
| (t1, t2, BoolT) -> t1 = t2;;

(* Vérifie que deux expressions sont bien du même type et qu'elles sont compatibles avec le if then else*)
let compareITEExp = function (t1, t2, t3) -> t1 = t2 & t1 = t3;;

(* Effectue l'avaluation des expressions contenues dans une liste*)
(*let rec evalExprList = function
([], _) -> []
| (t::r, env) -> tp_expr(t, env)::evalExprList(r, env);;*)

(* Récupère le type de l'appel de fonction dans l'environnement*)
let getTypeCallE = function (cVarList, Fundecl(eType , fName, fVarList), env) -> if (compareVarList(cVarList, fVarList, env)) then eType else raise BadCallType;;
	
(* Récupère le type d'expression *)							
let rec getType = function env -> function
(Const (_, constVal)) -> getTypeCons (constVal)
| (VarE (_, Var(vType, vName))) -> getTypeVar env (Var(vType,vName))
| (BinOp (_, binop, exp1, exp2)) -> let t1 = getType env exp1 and t2 = getType env exp2 and t3 = getTypeBinOp(binop) in if(compareBOExp (t1, t2, t3)) then t3 else raise BadType
| (IfThenElse (_, exp1, exp2, exp3)) -> let t1 = getType env exp1 and t2 = getType env exp2 and t3 = getType env exp3 in if(compareITEExp (t1, t2, t3)) then t1 else raise BadType
| (CallE (cEType, name, varList)) -> let fundecl = getFundecl(name, env.funbind) and typeList = List.map (getType env) varList in getTypeCallE(typeList, fundecl, env);;	
	
(* Evalue l'expression *)						
let rec tp_expr = function env -> function
(Const(_, constVal)) -> let  expType = getTypeCons (constVal) in Const (expType, constVal)
| (VarE(_, var)) -> let expType = getTypeVar env var in VarE(expType, var)
| (BinOp (eType, binop, exp1, exp2)) -> let expType = getType env (BinOp (eType, binop, exp1, exp2)) in BinOp (expType, binop, tp_expr env exp1, tp_expr env exp2)
| (IfThenElse (eType, exp1, exp2, exp3)) -> let expType = getType env (IfThenElse (eType, exp1, exp2, exp3)) in IfThenElse (expType, tp_expr env exp1, tp_expr env exp2, tp_expr env exp3)
| (CallE (cEType, name, varList)) -> let expType = getType env (CallE (cEType, name, varList)) and exprList = List.map (tp_expr env) varList in CallE (expType, name, exprList);;