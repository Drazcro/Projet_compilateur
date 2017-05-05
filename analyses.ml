(* Analyses of source language statements:
 - predicate: 'statement returns'
 - depth of operand stack for expression evaluation
 - definite assignment
*)

open Lang

(* Liste des erreurs pour l'analyse *)
type kindErrors = AssignException of string;;

(* Exception pour les variables n'existant pas *)
exception AnalyseError of kindErrors;;

(* ************************************************************ *)
(* ****  Statement returns                                 **** *)
(* ************************************************************ *)

(* Vérifie qu'un statement se termine bien *)
let rec stmt_returns = function
(Skip) -> false
|(Assign(_,_,_)) -> false
|(Seq(_,stmt)) -> stmt_returns stmt
|(Cond(_,stmt1, stmt2)) -> stmt_returns stmt1 && stmt_returns stmt2
|(While(_,stmt)) -> stmt_returns stmt
|(CallC(_,_)) -> false
|(Return _) -> true;;

(* ************************************************************ *)
(* ****  Stack depth                                       **** *)
(* ************************************************************ *)

(* Calcule la taille de la pille nécessaire pour les expressions *)
let rec stack_depth_e = function
(Const(_, _)) -> 1
|(VarE(_, _)) -> 1
|(BinOp(_, _, exp1, exp2)) -> max (stack_depth_e exp1) ((stack_depth_e exp2)+1)
|(IfThenElse(_, exp1, exp2, exp3)) -> List.fold_left max 2 [stack_depth_e exp1; stack_depth_e exp2; stack_depth_e exp3]
|(CallE(_, _, eList)) -> let sList = List.map stack_depth_e eList 
		         in List.fold_left max 0 sList + List.length sList;;

(* Calcule la taille de la pille nécessaire pour les instructions *)
let rec stack_depth_c = function
(Skip) -> 0
|(Assign(_,_,exp)) -> stack_depth_e exp
|(Seq(stmt1,stmt2)) -> max (stack_depth_c stmt1) (stack_depth_c stmt2)
|Cond(exp,stmt1,stmt2) -> List.fold_left max 2 [stack_depth_e exp; stack_depth_c stmt1; stack_depth_c stmt2]
|(While(exp,stmt)) -> max 2 (max (stack_depth_e exp) (stack_depth_c stmt))
|(CallC(_,eList)) -> let sList = List.map stack_depth_e eList 
		     in List.fold_left max 0 sList + (List.length sList)
|(Return exp) -> stack_depth_e exp;;

(* ************************************************************ *)
(* ****  Definite Assignment                               **** *)
(* ************************************************************ *)

module StringSet = 
  Set.Make
    (struct type t = string 
	    let compare = Pervasives.compare 
     end)

(* Permet de faire la vérification defassign_e sur une liste d'expressions *)
let rec defassignTable = fun f eList -> match eList with
([]) -> true
| (t::r) -> if f t = true 
	    then defassignTable f r
	    else false;; 

(* Verifie que l'expression a bien une valeur finale *)
let rec defassign_e = fun vs exp -> match exp with
(Const(_, _)) -> true
|(VarE(_,Var(_, n))) -> StringSet.mem n vs
|(BinOp(_, _, exp1, exp2)) -> defassign_e vs exp1 && defassign_e vs exp2
|(IfThenElse(_, exp1, exp2, exp3)) -> defassign_e vs exp1 && defassign_e vs exp2 && defassign_e vs exp3
|(CallE(_, _, eList)) -> defassignTable (defassign_e vs) eList;;

(* Verifie que l'instruction a bien une valeur finale et renvoie les variables ayant une valeur prédefinie *)
let rec defassign_c = fun allvs stmt -> match stmt with
(Skip) -> allvs
|(Assign (_, Var(_,n), exp)) -> if (defassign_e allvs exp) 
			           then StringSet.add n allvs
			           else raise (AnalyseError(
					       AssignException("Erreur d'assignation : 
                                                                l'expression est indefinie !")))
|(Seq(stmt1, stmt2)) -> let allvs = defassign_c allvs stmt1 
		        in defassign_c allvs stmt2
|(Cond(exp, stmt1, stmt2)) -> if (defassign_e allvs exp) 
			      then let s1 = defassign_c allvs stmt1 
			           in let s2 = defassign_c allvs stmt2 
			  	      in StringSet.inter s1 s2
     			      else raise (AnalyseError(
				          AssignException("Erreur d'assignation : 
							   l'expression est indefinie !")))
|(While(exp, stmt)) -> if (defassign_e allvs exp) 
		       then let allvs = defassign_c allvs stmt
			    in allvs 
     		       else raise (AnalyseError(
				   AssignException("Erreur d'assignation : 
						    l'expression est indefinie !")))
|(CallC (_, eList)) -> let dList = List.map (defassign_e allvs) eList 
			  in if List.exists not dList
			     then raise (AnalyseError(
					 AssignException("Erreur d'assignation : 
							  l'expression est indefinie !")))
     			     else allvs
|(Return exp) -> if (defassign_e allvs exp) 
	         then allvs
	         else raise (AnalyseError(
			      AssignException("Erreur d'assignation : 
						          l'expression est indefinie !")));;
