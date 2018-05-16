type variable=X of string;;
type sym= Sym of string*int;; (*int is the arrity*)
type term= V of variable|Func of atom
and atom= P_sym of sym*(term list);;
(* type body=Body of atom list;; *)
type body=Body of term list;; (* Only term like Func of atom no V of variable *)
type head=Head of term;; (* Only term like Func of atom no V of variable *)
(* type head=Head of atom;; *)
type clause =Fact of head|Rule of head*body;;
type program= Prog of clause list;;
type goal=Goal of term list;;(* only Func atom  *)
type cut =CUT;;
type answer= Tr|Fa|T of term list;;(* In the terms it will be consts only, I think so! *)

exception ERRor;;
exception NOT_UNIFIABLE;;
exception Fail;;


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
						else raise ERRor(* don't catch this error ,it will occur only if term are not well formed *)

;;



let id =fun x->x;;
(* initializze ans with id *)
				

let replace l r=match l with
	|[]->l
	|h::tail->r::tail
;;

let rec and_on_list l=match l with 
	|[]->true
	|h::tail->h && (and_on_list tail)
;;

let rec perfect_solve (d,rp,fp,gl,mgu_ans,bool_ans)=
				match (d,rp,gl) with
				|(_,_,[])-> 
							(	match bool_ans with
								|false::b'->mgu_ans,b'
							)
				|([],[],h::gl')-> (mgu_ans,(bool_ans))  (* simply false *)
				(* |((rmp,mgu_a,gl',bool_ll)::s',[],_)->perfect_solve(s',rmp,fp,gl',mgu_a,bool_ll) *)(* This can be added for multiple solutions *)
				|(s,rp,cg::gl')->let rec go_through prg cg =
										(match prg with
										|[]-> 
												(	match s with 
													|[]->(mgu_ans,(bool_ans))(* simply returing false *)
													|(prg',mgu_a,gl'',bool_l)::s'->perfect_solve(s',prg',fp,gl'',mgu_a,bool_l)

												)


										| Fact(Head(t))::prg' -> 
											(	try 
													let unif=(mgu t cg) in
													perfect_solve((prg',mgu_ans,gl,bool_ans)::s,fp,fp,(List.map (subst unif) gl'),compose mgu_ans unif,false::(replace bool_ans (true)) )
												with
												|_->go_through prg' cg
											)
										| (Rule(Head(t1),Body sub_gl ))::prg' ->
											(	try 
													let unif= (mgu t1 cg) in
													let unified_sub_goal =List.map (subst unif) sub_gl in
													let answer=perfect_solve(s,fp,fp,unified_sub_goal,compose mgu_ans unif,[false]) in
													let b_res=	match answer with
																|(funn,bool_l)->funn,[(and_on_list bool_l)]
																				(* (	match bool_l with 
																					|h::b->funn,[(and_on_list b)]
																				)	 *)
													in
													let a_unif,b=b_res in
													(* Printf.printf "%b\n" (List.hd b); *)
													if b=[true] then
														let unified_gl'=List.map (subst a_unif) gl' in
														perfect_solve((prg',mgu_ans,gl,bool_ans)::s,fp,fp,unified_gl',compose mgu_ans a_unif,false::(replace bool_ans (true)))
													else
														(
															(* a_unif,b; *)
															go_through prg' cg
														)

												with	
												|_->(* Printf.printf "Didn't unify\n"; *)
													go_through prg' cg

											)
										) in 
										go_through rp cg
				(* |_->raise ERRor *)

;;



let find_var gl=
		match gl with
		| Goal goal->
						let rec find_v goal=
								(	match goal with
								|[]->[]
								|V (X s)::g'->[V (X s)]@(find_v g')
								|Func(P_sym(Sym(s,n),l))::g'->(find_v l)@(find_v g')
						)in find_v goal
;;


let rec getresult sigma vl=
		match vl with
		| [] -> []
		| fst::rst -> (fst,subst sigma fst)::(getresult sigma rst)
		| _->raise ERRor
;;

let rec get_all_result sig_lt vl=
		match sig_lt with
		| [] -> []
		| fst::rst -> (getresult fst vl)::(get_all_result rst vl)
		;;


let perfect_run_prolog prg gl= match prg,gl with
							| (Prog l),(Goal gll) -> perfect_solve ([],(List.rev l),(List.rev l),gll,id,[false])
;;


let run program goal_list=
							let a,c=(perfect_run_prolog program goal_list) in
							(* Printf.printf "%d\n" (List.length (List.hd (get_all_result [a] (find_var goal_list)))); *)
							match (get_all_result [a] (find_var goal_list)),c with 
							|[[]],(r::c')->	(
												if r =false then
														Printf.printf "false.\n"
												else 
														Printf.printf "true.\n"	
											)

							| (l::t),(r::c')->		(
														if r =false then
															Printf.printf "false.\n"
														else
														(	
															(   
																let plist (h,a) =
																			(	match h with 
																				|V(X s)->	(	match a with 
																								|Func(P_sym(Sym(s_n,0),[]))->Printf.printf "%s = %s\n" s s_n
																								|V(X s')->Printf.printf "%s = %s\n" s s'
																								|_-> Printf.printf "Something wrong\n"
																							)
																				|_->Printf.printf "Something wrong\n"
																			)
																in List.map plist l
															)
															;
															Printf.printf "true.\n"
														)
													)
;;



(* TestCases *)
let program1=Prog 
[
Fact 	( Head	(
					Func(P_sym(Sym("Coder",1),[Func (P_sym (Sym("Rahul",0),[]))]))

				)
		)

;
Fact 	( Head	(
					Func(P_sym(Sym("Coder",1),[Func (P_sym (Sym("Shubham",0),[]))]))

				)
		)
;
Rule (
	   Head(
	   		Func(P_sym(Sym("friends",2),[V (X "X");V (X "Y")]))
	   )
	   ,
	   Body(
	   		[Func(P_sym(Sym("Coder",1),[V (X "X")]))
	   		;
	   		Func(P_sym(Sym("Coder",1),[V (X "Y")]))
	   		]

	   )

	)

]
;;



let goal_list= Goal [
	Func(P_sym(Sym("friends",2),[Func (P_sym (Sym("Shubham",0),[]));V (X "Z") ]))

]
;;


let term3 =Func (P_sym (Sym("Add",2),[V (X "X");Func (P_sym (Sym("Mul",2),[V (X "Y");Func (P_sym (Sym("Mul",2),[V (X("X"));V (X "Y")]))]))]))
let term12=Func (P_sym (Sym("Add",2),[V (X "Z");Func (P_sym (Sym("Mul",2),[V (X "Z");Func (P_sym (Sym("Mul",2),[V (X("X"));V (X "Y")]))]))]))
;;
let lt=Goal [term3;term12];;
