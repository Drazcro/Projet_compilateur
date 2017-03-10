(* Compilation functions *)

open Lang
open Analyses
open Instrs
open Print_instr

(* ************************************************************ *)
(* **** Compilation of expressions / statements            **** *)
(* ************************************************************ *)

(* Quand une variable n'a pas été trouvée *)
exception NotFound;;
(* Quand l'expression ne peut pour l'instant être traduite en bytecode *)
exception NotSuported;;
	
(* Fonction auxilliaire de position *)
let rec positionAux = function 
(_, _, []) -> raise NotFound
|(elm, cpt, (t::r)) -> if (elm = t) 
		       then cpt 
		       else positionAux(elm, cpt+1, r);;

(* Récupère la position d'un élément dans la liste *)
let position = fun elm list -> positionAux(elm, 0, list);;

(* Transforme une expression en un tableau de bytecode lisible par Jasmin *)
let rec gen_exp = fun vList exp -> match exp with
(Const(IntT, IntV(v))) -> [pr_instr(Loadc(IntT, IntV(v)))]
|(Const(BoolT, BoolV(v))) -> if(v = true) 
			     then [pr_instr(Loadc(BoolT, IntV (1)))] 
			     else [pr_instr(Loadc(BoolT, IntV(0)))]
|(VarE(_, Var(vType, vName))) -> [pr_instr(Loadv(IntT, (position vName vList)))]
|(BinOp(_, BCompar(_),exp1,exp2)) -> raise NotSuported
|(BinOp(_, op,exp1,exp2)) -> let l1 = (gen_exp vList exp1) 
			     and l2 = (gen_exp vList exp2) in 
					                   l1@l2@[pr_instr(Bininst(IntT,op))]
| _ -> raise NotSuported;;

(* ************************************************************ *)
(* **** Compilation of methods / programs                  **** *)
(* ************************************************************ *)

let gen_prog (Prog (gvds, fdfs)) = 
  JVMProg ([], 
           [Methdefn (Methdecl (IntT, "even", [IntT]),
                      Methinfo (3, 1),
                      [Loadc (IntT, IntV 0); ReturnI IntT])]);;
				
