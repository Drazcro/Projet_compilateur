(* Compilation functions *)

open Lang
open Analyses
open Instrs

(* ************************************************************ *)
(* **** Compilation of expressions / statements            **** *)
(* ************************************************************ *)
exception NotFound;;
exception NotSuported;;
	
let rec positionAux = function 
(_, _, []) -> raise NotFound
|(elm, cpt, (t::r)) -> if (elm = t) 
		       then cpt 
		       else positionAux(elm, cpt+1, r);;

	
let position = fun elm list -> positionAux(elm, 0, list);;

let rec gen_exp = fun vList exp -> match exp with
(Const(IntT, IntV(v))) -> [Loadc(IntT, IntV(v))]
<<<<<<< HEAD
|(Const(BoolT, BoolV(v))) -> if(v = true) 
			     then [Loadc(BoolT, IntV (1))] 
			     else [Loadc(BoolT, IntV(0))]
|(VarE(_, Var(vType, vName))) -> [Loadv(IntT, (position vName vList))]
|(BinOp(_, BCompar(_),exp1,exp2)) -> raise NotSuported
|(BinOp(_, op,exp1,exp2)) -> let l1 = (gen_exp vList exp1) 
			     and l2 = (gen_exp vList exp2) in 
					                   l1@l2@[Bininst(IntT,op)]
| _ -> raise NotSuported;;

(* ************************************************************ *)
(* **** Compilation of methods / programs                  **** *)
(* ************************************************************ *)

let gen_prog (Prog (gvds, fdfs)) = 
  JVMProg ([], 
           [Methdefn (Methdecl (IntT, "even", [IntT]),
                      Methinfo (3, 1),
                      [Loadc (IntT, IntV 0); ReturnI IntT])]);;
				
