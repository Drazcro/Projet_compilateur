(* Typechecking of source programs *)

#use "lang.ml"
#use "analyses.ml"

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

exception BadCallType;;

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

(* *)
let rec getFundecl = function
(_, []) -> raise FunNotDefined
|(name, Fundecl(eType , fName, varList)::r) -> if(name = fName) then Fundecl(eType , fName, varList) else getFundecl(name, r);;

let rec compareVarList = function
([], [], _) -> true
| ([], _, _) -> false
| (_, [], _) -> false
| (ct::cr, Vardecl(eVType , _)::fr, env) -> let eCType = getType(ct, env) in if(eCType =eVType) then compareVarList(cr, fr, env) else false;;

let getTypeCallE = function (CallE (cEType, name, cVarList), Fundecl(eType , fName, fVarList), env) -> let exprList = evalExprList(cVarList, env) in if (compareVarList(exprList, fVarList, env)) then eType else raise BadCallType;;
							
(* Récupère le type d'expression *)							
let rec getType = function
(Const (_, constVal), env) -> getTypeCons (constVal)
| (VarE (_, Var(vType, vName)), env) -> getTypeVar env (Var(vType,vName))
| (BinOp (_, binop, exp1, exp2), env) -> let t1 = getType (exp1,env) and t2 = getType (exp2,env) and t3 = getTypeBinOp(binop) in if(compareBOExp (t1, t2, t3)) then t3 else raise BadType
| (IfThenElse (_, exp1, exp2, exp3), env) -> let t1 = getType (exp1, env) and t2 = getType (exp2, env) and t3 = getType (exp3, env) in if(compareITEExp (t1, t2, t3)) then t1 else raise BadType
| (CallE (cEType, name, varList), env) -> let fundecl = getFundecl(name, env.funbind) in getTypeCallE(CallE (cEType, name, varList), fundecl, env);;
 
(* Vérifie que deux expressions sont bien du même type et qu'elles sont compatibles avec l'opération binaire*)
let compareBOExp = function 
(t1, t2, IntT) -> t1 = t2 & t1 = IntT
| (t1, t2, BoolT) -> t1 = t2;;

(* Vérifie que deux expressions sont bien du même type et qu'elles sont compatibles avec le if then else*)
let compareITEExp = function (t1, t2, t3) -> t1 = t2 & t1 = t3;;
					
let rec evalExprList = function
([], _) -> []
| (t::r, env) -> tp_expr(t, env)::evalExprList(r, env);;
					
(* Evalue l'expression *)						
let rec tp_expr = function 
(Const(_, constVal), env) -> let  expType = getTypeCons (constVal) in Const (expType, constVal)
| (VarE(_, var), env) -> let expType = getTypeVar env var in VarE(expType, var)
| (BinOp (eType, binop, exp1, exp2), env) -> let expType = getType (BinOp (eType, binop, exp1, exp2), env) in BinOp (expType, binop, tp_expr(exp1, env), tp_expr(exp2, env))
| (IfThenElse (eType, exp1, exp2, exp3), env) -> let expType = getType (IfThenElse (eType, exp1, exp2, exp3), env) in IfThenElse (expType, tp_expr(exp1, env), tp_expr(exp2, env), tp_expr(exp3, env))
| (CallE (cEType, name, varList), env) -> let expType = getType(CallE (cEType, name, varList), env) and exprList = evalExprList(varList, env) in CallE (expType, name, exprList);;