(* Compilation functions *)

open Lang
open Analyses
open Instrs

(* ************************************************************ *)
(* **** Compilation of expressions / statements            **** *)
(* ************************************************************ *)

(* Quand une variable n'a pas été trouvée *)
exception NotFound;;

(* Quand l'expression ne peut pour l'instant être traduite en bytecode *)
exception NotSuported;;

(* Pointeur explicite de caml servant à stocker la dernière étiquette utilisable *)
let lastLabel = ref 0;;

(* Fonction impérative servant à la fois à incrémenter le pointeur et à renvoyer le dernier label sous la forme valide *)
let getLastLabel = function () -> incr lastLabel; [!lastLabel];;

(* Convertie les types bool en int *)
let convertInIntT = function tp -> if tp = BoolT 
				      then IntT 
				      else tp;;

(* Fonction auxilliaire de position *)
let rec positionAux = function 
(_, _, []) -> raise NotFound
|(elm, cpt, (t::r)) -> if elm = t 
		       then cpt 
		       else positionAux(elm, cpt+1, r);;

(* Récupère la position d'un élément dans la liste *)
let position = fun elm list -> positionAux(elm, 0, list);;

(* Génère le pseudo bytecode pour une expression *)
let rec gen_exp = fun vList exp -> match exp with
(Const(IntT, v)) -> [Loadc(IntT, v)]
|(Const(BoolT, BoolV(v))) -> if v = true 
			      then [Loadc(IntT, IntV 1)]
			      else [Loadc(IntT, IntV 0)]
|(VarE(t, Var(vt,n))) -> if vt = Local 
			  then let posV = position n vList 
	 	 	       in [Loadv(IntT, posV)]
			  else [Getstatic(IntT, n)]
|(BinOp (_, BCompar(op), exp1, exp2)) -> let trueLabel = getLastLabel()
					  and endLabel = getLastLabel() 
					  in let ge1 = gen_exp vList exp1 
				  	     in let ge2 = gen_exp vList exp2
					  	in ge1@ge2@If(op, trueLabel)::Loadc(IntT, IntV 0)
				             	::Goto endLabel::Label trueLabel::Loadc(IntT, IntV 1)::[Label(endLabel)]
|(BinOp (_, op, exp1, exp2)) -> let ge1 = gen_exp vList exp1
				 in let ge2 = gen_exp vList exp2
			 	    in ge1@ge2@[Bininst(IntT, op)]
|(IfThenElse(_, exp1, exp2, exp3)) -> let trueLabel = getLastLabel()
				       and endLabel = getLastLabel() 
				       in let ge1 = gen_exp vList exp1 
   	               		       in let ge2 = gen_exp vList exp2
			               in let ge3 = gen_exp vList exp3
				       in ge1@Loadc(IntT, IntV 1)::If(BCeq, trueLabel)
					  ::ge3@Goto endLabel::Label trueLabel::ge2@[Label endLabel]
|CallE(t, n, eList) ->  let geList = List.concat (List.map (gen_exp vList) eList)
			 and newT = convertInIntT t
	             	 and tList = List.map convertInIntT (List.map tp_of_expr eList) 
	                 in geList@[Invoke(newT,n,tList)]
| _ -> raise NotSuported;;

(* Génère le pseudo bytecode pour un statement *)
let rec gen_stmt = fun vList stmt -> match stmt with
(Skip) -> [Nop]
|(Assign(t, Var(vt,n), exp)) -> let ge = gen_exp vList exp 
				in if vt = Local 
		      		   then let posV = position n vList 
					in ge@[Storev(IntT, posV)]
		      		   else ge@[Putstatic(IntT, n)]
|(Seq(stmt1, stmt2)) -> gen_stmt vList stmt1@gen_stmt vList stmt2
|(Cond(exp, stmt1, stmt2)) -> let trueLabel = getLastLabel()
			      and endLabel = getLastLabel() 
			      and ge = gen_exp vList exp
			      and gstmt1 = gen_stmt vList stmt1
			      and gstmt2 = gen_stmt vList stmt2
			      in ge@Loadc(IntT, IntV 1)::If(BCeq, trueLabel)::gstmt2@Goto endLabel
			         ::Label trueLabel::gstmt1@[Label endLabel]
| (While(exp, stmt)) -> let whileLabel = getLastLabel()
		        and endLabel = getLastLabel() 
			and ge = gen_exp vList exp 
		        and gstmt = gen_stmt vList stmt 
		        in Label whileLabel::ge@Loadc(IntT, IntV 0)::If(BCeq, endLabel)::gstmt@Goto whileLabel::[Label endLabel]
| (CallC(n, eList)) -> let geList = List.concat (List.map (gen_exp vList) eList)
	             	 and tList = List.map convertInIntT (List.map tp_of_expr eList) 
	                 in geList@[Invoke(VoidT,n,tList)]
| (Return (Const(VoidT,_))) -> [ReturnI VoidT]
| (Return (exp)) -> let ge = gen_exp vList exp in ge@[ReturnI (convertInIntT (tp_of_expr exp))];;


(* Génère le pseudo bytecode pour une definition de fonction *)
let gen_fundefn = fun (Fundefn(Fundecl(t,n, pList), vList, body)) ->
let tList = List.map tp_of_vardecl pList 
in let mdecl = Methdecl(convertInIntT t, n, List.map convertInIntT tList) 
   and meinfo = Methinfo(Analyses.stack_depth_c body, (List.length pList + List.length vList))
   and gstmt = gen_stmt (List.map name_of_vardecl (pList@vList)) body
   in Methdefn(mdecl,meinfo, gstmt);;

(* ************************************************************ *)
(* **** Compilation of methods / programs                  **** *)
(* ************************************************************ *)

(* Génère le pseudo bytecode pour un programme *)
let gen_prog (Prog (gvds, fdfs)) = 
  JVMProg(gvds,List.map gen_fundefn fdfs);;
