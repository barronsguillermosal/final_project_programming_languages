:- op( 500, fy, ~). % negation
:- op(1000, xfy, &). % conjunction
:- op(1100, xfy, '|'). % disjunction
:- op(1110, xfy, =>). % implication
:- op( 500, fy, !). % universal quantifier: ![X]:
:- op( 500, fy, ?). % existential quantifier: ?[X]:
:- op( 500,xfy, :).

prove_interface(F):-
	prove([]>[F],[]).

select1(X,L,L1):-
	append(L2,[X|L3],L),
	append(L2,L3,L1).

%Only axiom for sequents
prove(G>D,_):-
	member(A,G),
	member(B,D),
	unify_with_occurs_check(A,B).

%Transformation according to left conjunction rule
prove(G>D,FV):-
	select1(A&B,G,G1),
	!,
	prove([A,B|G1]>D,FV).

%Transformation according to right conjuntion rule
prove(G>D,FV):-
	select1(A&B,D,D1),
	!,
	prove(G>[A|D1],FV),
	prove(G>[B|D1],FV).

%Transformation according to left disjunction rule
prove(G>D,FV):-
	select1(A|B,G,G1),
	!,
	prove([A|G1]>D,FV),
	prove([B|G1]>D,FV).

%Transformation according to right disjunction rule
prove(G>D,FV):-
	select1(A|B,D,D1),
	!,
	prove(G>[A,B|D1],FV).

%Transformation according to left implication rule
prove(G>D,FV):-
	select1(A=>B,G,G1),
	!,
	prove(G1>[A|D],FV),
	prove([B|G1]>D,FV).

%Transformation according to right implication rule
prove(G>D,FV):-
	select1(A=>B,D,D1),
	!,
	prove([A|G]>[B|D1],FV).

%Transformation according to left negation rule
prove(G>D,FV):-
	select1(~A,G,G1),
	!,
	prove(G1>[A|D],FV).

%Transformation according to the right negation rule
prove(G>D,FV):-
	select1(~A,D,D1),
	!,
	prove([A|G]>D1,FV).

%Transformation according to the left universal quantifier rule
prove(G>D,FV):-
	member((![X]:A),G),
	copy_term((X:A,FV),(Y:A1,FV)),
	prove([A1|G]>D,[Y|FV]).

%Transformation according to the right existential quantifier rule
prove(G>D,FV):-
	member((?[X]:A),D),
	copy_term((X:A,FV),(Y:A1,FV)),
	prove(G>[A1|D],[Y|FV]).