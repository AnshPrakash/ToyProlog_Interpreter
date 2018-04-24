
type variable=X of string;;
type sym= Sym of string*int;; (*int is the arrity*)
type term= V of variable|Func of atom
and atom= P_sym of sym*(term list);;
type body=Body of atom list;;
type head=Head of atom;;
type clause =Fact of head|Rule of head*body;;
type program= Prog of clause list;;
type goal=Goal of atom list;;

type answer= Tr|Fa|T of term list;;(* In the terms it will be consts only, I think so! *)

exception Error;;
exception NOT_UNIFIABLE;;
exception Fail;;

(* 
let rec subst substitution t=	match t with 
		|V v->	( let rec checkequ sub=(match  sub with
									|[]-> V v
									| hd::tl-> ( match hd with 
												|(a,b)-> if(a=t) then b else checkequ tl)
								   ) in checkequ substitution
				)
		|Func (P_sym (Sym(s,n),l))->if n=0 then t else Func (P_sym (Sym(s,n), List.map (subst substitution) l))
;;
 *)

let rec subst sigma t=match t with 
	|V v-> sigma t
	|Func (P_sym (Sym(s,n),l))->if n=0 then t else Func (P_sym (Sym(s,n), List.map (subst sigma) l))
;;

let compose substitution1 substitution2  =
	    fun x -> subst substitution2 (subst substitution1 x)
;;

let oR x y=x||y;;

let rec find v t =
		match t with 
		|Func (P_sym (Sym(s,arrity),l))->if arrity =0 then false else List.fold_left oR false (List.map (find v) l)
		|V x-> if(v=t) then true else false
;;


let rec mgu term1 term2 = match  (term1,term2) with 
			|(V s1,V s2)->fun var -> if var=V s1 then V s2 else var
			(* |(V x,Func (P_sym (Sym(s,arrity),l)))->fun var->if var=x then Func (P_sym (Sym(s,arrity),l)) else V var *)
			|(V x,Func (P_sym (Sym(s,arrity),l)))-> if (find term1 term2) then raise NOT_UNIFIABLE else fun var -> if var=V x then Func (P_sym (Sym(s,arrity),l)) else var
			|(Func (P_sym (Sym(s1,0),[])),Func (P_sym (Sym(s2,0),[])))-> if s1=s2 then (fun var-> var) else raise NOT_UNIFIABLE
			|(Func (P_sym (Sym(s,ar),l)),V x)-> mgu term2 term1 
			(* |(Func (P_sym (Sym(s,0),[])),Func (P_sym (Sym(s1,arrity1),l1))) ->if arrity1<>0 then raise NOT_UNIFIABLE *)
			|(Func (P_sym (Sym(s1,arrity1),l1)),(Func (P_sym (Sym(s2,arrity2),l2))))->	
						if s1<>s2 then raise NOT_UNIFIABLE
						else if arrity1=arrity2  then
							List.fold_left2 (fun s a b -> compose s (mgu (subst s a) (subst s b)) ) (fun var-> var) l1 l2
						else raise Error(* don't catch this error ,it will occur only if term are not well formed *)

;;





let rec solve program query= match program with 
			| []->[Fa]
			| hd::tl-> 	let l=(unify hd query) in
						(	match l with
							|[]->[Tr]
							| _-> l
						)
;;

(* let solve pr= [Fa];; *)

let rec ans_queries goals program=match goals with
	| Goal l-> List.map (solve program) l
	|_->raise Error
;;
(*Test Case*)
let program1=Prog [Fact (Head (P_sym (Sym("man",1),[Func (P_sym (Sym("Rahul",0),[]))])))];;
let program2=Prog [Fact (Head (P_sym (Sym("boy",1),[Func (P_sym (Sym("Rahul",0),[]))])));Fact (Head (P_sym (Sym("boy",1),[Func (P_sym (Sym("Shubham",0),[]))])));Fact (Head (P_sym (Sym("friends",1),[Func (P_sym (Sym("Anubhav",0),[]));Func (P_sym (Sym("Shubham",0),[]))])));Rule (Head (P_sym (Sym("friends",2),[Func (P_sym (Sym("Anubhav",0),[]));Func (P_sym (Sym("Rahul",0),[]))])),Body [P_sym (Sym("friends",2),[ Func (P_sym (Sym("Anubhav",0),[])); Func (P_sym (Sym("Shubham",0),[]))])])];;

let program3=Prog [Fact (Head (P_sym (Sym("boy",1),[Func (P_sym (Sym("Rahul",0),[]))])));Fact (Head (P_sym (Sym("boy",1),[Func (P_sym (Sym("Shubham",0),[]))])));Fact (Head (P_sym (Sym("friends",1),[Func (P_sym (Sym("Anubhav",0),[]));Func (P_sym (Sym("Shubham",0),[]))])));Rule (Head (P_sym (Sym("friends",2),[Func (P_sym (Sym("Anubhav",0),[]));Func (P_sym (Sym("Rahul",0),[]))])),Body [P_sym (Sym("friends",2),[ V(X "X"); Func (P_sym (Sym("Shubham",0),[]))])])];;



let goals=Goal [P_sym (Sym("man",1),[V(X "X")])];;


let term3 =Func (P_sym (Sym("Add",2),[V (X "X");Func (P_sym (Sym("Mul",2),[V (X "Y");Func (P_sym (Sym("Mul",2),[V (X("X"));V (X "Y")]))]))]))
let term12=Func (P_sym (Sym("Add",2),[V (X "Z");Func (P_sym (Sym("Mul",2),[V (X "Z");Func (P_sym (Sym("Mul",2),[V (X("X"));V (X "Y")]))]))]))

subst (mgu term3 term12) term3;;
subst (mgu term3 term12) term12;;
subst (mgu term12 term3) term12;;
subst (mgu term12 term3) term3;;

(*http://cfbolz.de/Bolz2007-Bachelorarbeit.pdf*)



