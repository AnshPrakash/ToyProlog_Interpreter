

type variable=X of string;;
type sym= Sym of string*int;; (*int is the arrity*)
type atom= P_sym of sym*(term list);;
type term= Const of int| V of variable|Func of atom;;
type body=Body of atom list;;
type head=Head of atom;;
type clause =Fact of head|Rule of head*body;;
type program= Prog of clause list;;
type goal=Goal of atom list;;



(*http://cfbolz.de/Bolz2007-Bachelorarbeit.pdf*)



