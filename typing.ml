(* Typechecking of source programs *)

open Lang
open Analyses

(* Environments *)

type environment = 
    {localvar: (vname * tp) list; 
     globalvar: (vname * tp) list; 
     returntp: tp;
     funbind: fundecl list};;

type kindErrors = 
NotDefined of string (* Non défini *)
| BadType of string (* Mauvais typage *)
| BadNbArgs of string (* Mauvais nombre d'arguments *)
| BadCall of string (* Mauvais appel de fonction *)
| BadDef of string;; (* Mauvaise definition de fonction *)      		 

(* Exception pour les variables n'existant pas *)
exception TypingError of kindErrors;;

(* Récupère la variable dans le tableau *)
let rec getTypeVarAux = fun vList name -> match vList with
((vn, tp)::r) -> if vn = name 
                 then tp 
	         else getTypeVarAux r name
|([]) -> raise (TypingError(NotDefined("La variable "^name^" n'a pas été trouvée dans l'environnement.")));;

(* Récupère le type d'une variable dans l'environnement à partir d'un environnement et du nom d'une variable *)
let getTypeVar = fun env v -> match v with 
(Var(Local, vn)) -> getTypeVarAux env.localvar vn
|(Var(Global, vn)) -> getTypeVarAux env.globalvar vn;;

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

(* Récupère le type d'une déclaration de fonction *)
let getTypeFundecl = function Fundecl(t, _,_) -> t;;

(* Récupère la déclaration de fonction dans l'environnement *)
let rec getFundecl = fun fList name -> match fList with 
([]) -> raise (TypingError(NotDefined("La fonction "^name^" n'a pas été trouvée dans l'environnement.")))
|(Fundecl(t , fn, vList)::r) -> if name = fn 
			        then Fundecl(t , fn, vList) 
			        else getFundecl r name;;
						 
(* vérifie si les variables de la déclaration de fonction et celles de l'appel de la fonctions sont compatibles *)
let rec compareList = function
([], [], _) -> true
|([], _, _) -> false
|(_, [], _) -> false
|(t1::r1, t2::r2, env) -> if t1 = t2 
		          then compareList(r1, r2, env) 
		          else false;;
 
(* Vérifie que deux expressions sont bien du même type et qu'elles sont compatibles avec l'opération binaire *)
let compareBOExp = fun t1 t2 tBOExp -> match tBOExp with
(IntT) -> t1 = t2 && t1 = IntT
|(BoolT) -> t1 = t2
|(VoidT) -> false;;

(* Vérifie que les trois expressions utilisées dans la condition soient bien du même type *)
let compareITEExp = fun t1 t2 t3 -> t1 = t2 && t1 = t3;;

(* Récupère le type de l'appel de fonction dans l'environnement*)
let getTypeCallE = fun tList (Fundecl(eType , fName, fvList)) env -> 
let ftList = List.map tp_of_vardecl fvList 
in if compareList(tList, ftList, env) 
   then eType 
   else raise (TypingError(BadCall("La fonction "^fName^" n'a pu être appelée. 
		                    Les arguments sont invalides.")));; 

(* Récupère le type de l'expression *)							
let rec getType = fun env exp -> match exp with
(Const (_, v)) -> getTypeCons v
|(VarE (_, Var(t, n))) -> getTypeVar env (Var(t, n))
|(BinOp (_, binop, exp1, exp2)) -> let t1 = getType env exp1 
				   and t2 = getType env exp2 
				   and t3 = getTypeBinOp(binop) 
      				   in if (compareBOExp t1 t2 t3) 
				      then t3 
				      else raise (TypingError(BadType("Les expressions de l'op binaire sont invalides.")))
|(IfThenElse (_, exp1, exp2, exp3)) -> let t1 = getType env exp1 
				       and t2 = getType env exp2 
				       and t3 = getType env exp3 
				       in if(compareITEExp t1 t2 t3) 
					  then t1 
					  else raise (TypingError(BadType("Les expressions du ifthenelse sont invalides.")))
|(CallE (cEType, name, vList)) -> let fundecl = getFundecl env.funbind name 
				  and tList = List.map (getType env) vList 
				  in getTypeCallE tList fundecl env	
	
(* Evalue l'expression *)						
let rec tp_expr = fun env exp -> match exp with
(Const(_, v)) -> let  eType = getTypeCons (v) 
		 in Const (eType, v)
|(VarE(_, var)) -> let eType = getTypeVar env var 
 		   in VarE(eType, var)
|(BinOp (t, binop, exp1, exp2)) -> let eType = getType env (BinOp (t, binop, exp1, exp2)) 
				   in BinOp (eType, binop, tp_expr env exp1, tp_expr env exp2)
|(IfThenElse (t, exp1, exp2, exp3)) -> let eType = getType env (IfThenElse (t, exp1, exp2, exp3)) 
				       in IfThenElse (eType, tp_expr env exp1, tp_expr env exp2, tp_expr env exp3)
|(CallE (t, name, vList)) -> let eType = getType env (CallE (t, name, vList)) 
			     and eList = List.map (tp_expr env) vList 
			     in CallE (eType, name, eList);;

(* Evalue une instruction *)
let rec tp_stmt = fun env stmt -> match stmt with
(Skip) -> Skip
| (Assign(t, var, expr)) -> let typeVar = getTypeVar env var 
			    in let evalExp = tp_expr env expr 
			       in if typeVar <> tp_of_expr evalExp 
				  then raise(TypingError(BadType("La variable et l'expression 
							          ont un type different !")))
			       else Assign(VoidT, var, evalExp)
| (Seq(stmt1, stmt2)) -> Seq(tp_stmt env stmt1, tp_stmt env stmt2)
| (Cond(expr, stmt1, stmt2)) -> let evalExp = tp_expr env expr 
				in let t = tp_of_expr evalExp 
				   in if t <> BoolT 
				      then raise(TypingError(BadType("La condition doit être booléenne !")))
				      else Cond(evalExp, tp_stmt env stmt1, tp_stmt env stmt2)
| (While(expr, stmt)) -> let evalExp = tp_expr env expr
			 in let t = tp_of_expr evalExp 
			    in if t <> BoolT 
			       then raise(TypingError(BadType("Le while doit être booléen !")))
   			       else While(evalExp, tp_stmt env stmt)
| (CallC(name, eList)) -> let f = getFundecl env.funbind name 
			  in if getTypeFundecl f <> env.returntp 
			     then raise(TypingError(BadType("La fonction ne renvoie pas le bon type !")))
	  		     else let evaleList = List.map(tp_expr env) eList 
		     		  in let tList = List.map(getType env) evaleList 
				     and tFList = List.map (tp_of_vardecl) (params_of_fundecl f) 
				     in if(compareList(tList, tFList, env)) 
					then CallC(name, evaleList)		
                  			else raise(TypingError(BadCall("L'appel de la fonction 
									n'est pas valide avec sa 
									déclaration.")))
| (Return (expr)) -> let evalExp = tp_expr env expr
		     in let t = tp_of_expr evalExp 
		     in if(t = env.returntp) 
			then Return (evalExp)
		        else raise(TypingError(BadType("Le return ne retourne pas le bon type !")));;	 

(* Teste si le type de la variable est valide *)
let rec isVarValid = function
([]) -> true
|(t::r) -> if t = VoidT 
	   then false 
	   else isVarValid r;; 

(* Supprime une variable de la liste *)
let rec remove = fun name vList -> match vList with
([]) -> []
| (t::r) -> if name_of_vardecl t = name 
	    then remove name r 
	    else t::(remove name r);;  

(* Fonction auxiliaire de isUnique *)
let rec isUniqueAux = fun name vList -> match vList with
([]) -> []
|(t::r) -> let n = name_of_vardecl t 
	   in if name = n 
	      then t::(isUniqueAux name r) 
	      else isUniqueAux name r;;

(* Regarde qu'une variable soit bien unique dans les paramètres de déclaration d'une fonction *)
let rec isUnique = function
([]) -> true
|(t::r) -> let nb = List.length (isUniqueAux (name_of_vardecl t) (t::r)) 
	   in if nb = 1 
	      then  isUnique (remove (name_of_vardecl t) (t::r)) 
	      else false;;

(* Fonction auxillaire de addLocalVar *)
let rec addLocalVarAux = function
([]) -> []
|(Vardecl(t,n)::r) -> (n,t)::addLocalVarAux(r);;

(* Ajoute les vairaibles locales à un environnement *)
let addLocalVar = fun env vList -> let localvar = addLocalVarAux vList 
				   in let nlocalvar = localvar 
				      in {localvar = nlocalvar; globalvar = env.globalvar; 
				          returntp = env.returntp; funbind = env.funbind};;

(* Ajoute le type de retour à l'environnement *)
let addReturnTp = fun env fundecl -> {localvar = env.localvar; globalvar = env.globalvar; 
				      returntp = (getTypeFundecl fundecl); funbind = env.funbind};;

(* Ajoute les variables globales à l'environnement *)
let addGlobalVar = fun env vList -> let globalVar = addLocalVarAux vList 
				    in  {localvar = env.localvar; globalvar = globalVar; 
					 returntp = env.returntp; funbind = env.funbind};;
(* Fonction auxilliaire de addFundecl *)
let rec addFundeclAux = function
([]) -> []
| (Fundefn(fundecl, _, _)::r) -> fundecl::addFundeclAux(r);;

(* Ajoute les déclarations de fonctions à l'environnement *)
let addFundecl = fun env fList -> let nfunbind = addFundeclAux (fList) 
				  in {localvar = env.localvar; globalvar = env.globalvar; 
				      returntp = env.returntp; funbind = nfunbind};;

(* Evalue une definition de fonction *) 
let rec tp_fdefn = fun env (Fundefn(fundecl, vList, body)) -> 
let tList = List.map tp_of_vardecl vList @ List.map tp_of_vardecl (params_of_fundecl fundecl) 
in if (isVarValid tList) then let varList = vList@(params_of_fundecl fundecl) 
			      in if (isUnique varList) 
				 then let nEnv = addReturnTp (addLocalVar env varList) fundecl 
				      in Fundefn(fundecl, vList, tp_stmt nEnv body)
				 else raise (TypingError(BadDef("une ou plusieurs variables utilisées pour 
							   la definition de la fonction ne sont pas uniques.")))
   else raise (TypingError(BadDef("une ou plusieurs variables utilisées pour la 
			     definition de la fonction sont invalides.")));;

(* Evalue un programme *)
let tp_prog = fun (Prog(vList, fList)) -> let env = {localvar =[]; globalvar= []; returntp = VoidT; funbind = []} 
					  in Prog(vList, (List.map (tp_fdefn (addFundecl (addGlobalVar env vList) fList)) fList));;
