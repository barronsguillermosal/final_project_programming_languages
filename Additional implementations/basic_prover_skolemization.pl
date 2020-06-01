:- op( 500, fy, ~). % negation
:- op(1000, xfy, &). % conjunction
:- op(1100, xfy, '|'). % disjunction
:- op(1110, xfy, =>). % implication
:- op( 500, fy, !). % universal quantifier: ![X]:
:- op( 500, fy, ?). % existential quantifier: ?[X]:
:- op( 500,xfy, :).

prove_interface(F):-
	prove_interface_iterative(F,1).

prove_interface_iterative(F,I):-
	prove([]>[F],[],I,1,_).

prove_interface_iterative(F,I):-
	I1 is I+1,
	prove_interface_iterative(F,I1).

select1(X,L,L1):-
	append(L2,[X|L3],L),
	append(L2,L3,L1).

%Only axiom for sequents
prove(G>D,_,_,J,J):-
	member(A,G),
	A\=(_&_),
	A\=(_|_),
	A\=(_=>_),
	A\=(~_),
	A\=(!_),
	A\=(?_),
	member(B,D),
	unify_with_occurs_check(A,B).

%Transformation according to left conjunction rule
prove(G>D,FV,I,J,K):-
	select1(A&B,G,G1),
	!,
	prove([A,B|G1]>D,FV,I,J,K).

%Transformation according to right conjuntion rule
prove(G>D,FV,I,J,K):-
	select1(A&B,D,D1),
	!,
	prove(G>[A|D1],FV,I,J,J1),
	prove(G>[B|D1],FV,I,J1,K).

%Transformation according to left disjunction rule
prove(G>D,FV,I,J,K):-
	select1(A|B,G,G1),
	!,
	prove([A|G1]>D,FV,I,J,J1),
	prove([B|G1]>D,FV,I,J1,K).

%Transformation according to right disjunction rule
prove(G>D,FV,I,J,K):-
	select1(A|B,D,D1),
	!,
	prove(G>[A,B|D1],FV,I,J,K).

%Transformation according to left implication rule
prove(G>D,FV,I,J,K):-
	select1(A=>B,G,G1),
	!,
	prove(G1>[A|D],FV,I,J,J1),
	prove([B|G1]>D,FV,I,J1,K).

%Transformation according to right implication rule
prove(G>D,FV,I,J,K):-
	select1(A=>B,D,D1),
	!,
	prove([A|G]>[B|D1],FV,I,J,K).

%Transformation according to left negation rule
prove(G>D,FV,I,J,K):-
	select1(~A,G,G1),
	!,
	prove(G1>[A|D],FV,I,J,K).

%Transformation according to the right negation rule
prove(G>D,FV,I,J,K):-
	select1(~A,D,D1),
	!,
	prove([A|G]>D1,FV,I,J,K).

%Transformation according to the left universal quantifier rule
prove(G>D,FV,I,J,K):-
	member((![X]:A),G),
	\+ length(FV,I),
	copy_term((X:A,FV),(Y:A1,FV)),
	prove([A1|G]>D,[Y|FV],I,J,K).

%Transformation according to the right universal quantifier rule
prove(G>D,FV,I,J,K):-
	select1((![X]:A),D,D1),
	!,
	copy_term((X:A,FV),(f_sk(J,FV):A1,FV)),
	J1 is J+1,
	prove(G>[A1|D1],FV,I,J1,K).

%Transformation according to the left existential quantifier rule
prove(G>D,FV,I,J,K):-
	select1((?[X]:A),G,G1),
	!,
	copy_term((X:A,FV),(f_sk(J,FV):A1,FV)),
	J1 is J+1,
	prove([A1|G1]>D,FV,I,J1,K).	

%Transformation according to the right existential quantifier rule
prove(G>D,FV,I,J,K):-
	member((?[X]:A),D),
	\+ length(FV,I),
	copy_term((X:A,FV),(Y:A1,FV)),
	prove(G>[A1|D],[Y|FV],I,J,K).