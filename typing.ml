(* Typechecking of source programs *)

open Lang;;
open Analyses;;

(* Environments *)

type environment = 
    {localvar: (vname * tp) list; 
     globalvar: (vname * tp) list; 
     returntp: tp;
     funbind: fundecl list};;

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

let exp12 =
BinOp (0, BArith BAadd , VarE (0, Var (Local , "k")), Const(0, IntV 3));; 

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
let rec getTypeVarAux = function
((vn, tp)::r, vn2) -> if (vn = vn2) 
	              then tp 
		      else getTypeVarAux(r, vn2)
|([], _) -> raise VarNotDefined;;

(* Récupère le type d'une variable dans l'environnement à partir d'un environnement et du nom d'une variable *)
let getTypeVar = fun env v -> match v with 
(Var(Local, vn)) -> getTypeVarAux(env.localvar, vn)
|(Var(Global, vn)) -> getTypeVarAux(env.globalvar, vn);;

(* Récupère le type d'expression d'une constante *)
let getTypeCons = function
(IntV(_)) -> IntT
|(BoolV(_)) -> BoolT
|(VoidV) -> VoidT

(* Récupère le type d'expression d'une opération binaire *)
let getTypeBinOp = function
(BArith _) -> IntT
|(BCompar _) -> BoolT
|(BLogic _) -> BoolT;;

(* Récupère la déclaration de fonction dans l'environnement *)
let rec getFundecl = function
(_, []) -> raise FunNotDefined
|(n, Fundecl(t , fn, vList)::r) -> if(n = fn) 
			           then Fundecl(t , fn, vList) 
			           else getFundecl(n, r);;
						 
(* vérifie si les variables de la déclaration de fonction et celles de l'appel de la fonctions sont compatibles *)
let rec compareVarList = function
([], [], _) -> true
|([], _, _) -> false
|(_, [], _) -> false
|(ct::cr, Vardecl(t , _)::fr, env) -> if(ct = t) 
				      then compareVarList(cr, fr, env) 
				      else false;;
 
(* Vérifie que deux expressions sont bien du même type et qu'elles sont compatibles avec l'opération binaire *)
let compareBOExp = function 
(t1, t2, IntT) -> t1 = t2 && t1 = IntT
|(t1, t2, BoolT) -> t1 = t2
|(t1, t2, VoidT) -> true;;

(* Vérifie que les trois expressions utilisées dans la condition soient bien du même type *)
let compareITEExp = function (t1, t2, t3) -> t1 = t2 && t1 = t3;;

(* Récupère le type de l'appel de fonction dans l'environnement*)
let getTypeCallE = function (vList, Fundecl(eType , fName, fvList), env) -> 
if (compareVarList(vList, fvList, env)) 
then eType 
else raise BadCallType;;
	
(* Récupère le type de l'expression *)							
let rec getType = fun env exp -> match exp with
(Const (_, v)) -> getTypeCons (v)
|(VarE (_, Var(t, n))) -> getTypeVar env (Var(t, n))
|(BinOp (_, binop, exp1, exp2)) -> let t1 = getType env exp1 
				   and t2 = getType env exp2 
				   and t3 = getTypeBinOp(binop) in 
							        if(compareBOExp (t1, t2, t3)) 
	                                                        then t3 
							        else raise BadType
|(IfThenElse (_, exp1, exp2, exp3)) -> let t1 = getType env exp1 
				       and t2 = getType env exp2 
				       and t3 = getType env exp3 in 
								 if(compareITEExp (t1, t2, t3)) 
								 then t1 
								 else raise BadType
|(CallE (cEType, name, vList)) -> let fundecl = getFundecl(name, env.funbind) 
				  and tList = List.map (getType env) vList in 
									   getTypeCallE(tList, fundecl, env)	
	
(* Evalue l'expression *)						
let rec tp_expr = fun env exp -> match exp with
(Const(_, v)) -> let  eType = getTypeCons (v) in 
					      Const (eType, v)
|(VarE(_, var)) -> let eType = getTypeVar env var in 
						  VarE(eType, var)
|(BinOp (t, binop, exp1, exp2)) -> let eType = getType env (BinOp (t, binop, exp1, exp2)) in 
											  BinOp (eType, binop, tp_expr env exp1, tp_expr env exp2)
|(IfThenElse (t, exp1, exp2, exp3)) -> let eType = getType env (IfThenElse (t, exp1, exp2, exp3)) in 
												  IfThenElse (eType, tp_expr env exp1, tp_expr env exp2, tp_expr env exp3)
|(CallE (t, name, vList)) -> let eType = getType env (CallE (t, name, vList)) 
			     and eList = List.map (tp_expr env) vList in 
								      CallE (eType, name, eList);;

(* TODO: put your definitions here *)
let tp_prog (Prog (gvds, fdfs)) =
  Prog([],
       [Fundefn (Fundecl (BoolT, "even", [Vardecl (IntT, "n")]), [], Skip)])
;;
