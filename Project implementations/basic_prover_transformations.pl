:- op( 500, fy, ~). % negation
:- op(1000, xfy, &). % conjunction
:- op(1100, xfy, '|'). % disjunction
:- op(1110, xfy, =>). % implication
:- op( 500, fy, !). % universal quantifier: ![X]:
:- op( 500, fy, ?). % existential quantifier: ?[X]:
:- op( 500,xfy, :).

%Example of how to transform the antecedent of a sequent to use different axioms
%prove(G>D):-
%	select1(A,G,G'),
%	prove([A'|G']>D).

prove_interface(F):-
	prove([]>[F]).

select1(X,L,L1):-
	append(L2,[X|L3],L),
	append(L2,L3,L1).

%Only axiom for sequents
prove(G>D):-
	member(A,G),
	member(A,D).

%Transformation according to left conjunction rule
prove(G>D):-
	select1(A&B,G,G1),
	prove([A,B|G1]>D).

%Transformation according to right conjuntion rule
prove(G>D):-
	select1(A&B,D,D1),
	prove(G>[A|D1]),
	prove(G>[B|D1]).

%Transformation according to left disjunction rule
prove(G>D):-
	select1(A|B,G,G1),
	prove([A|G1]>D),
	prove([B|G1]>D).

%Transformation according to right disjunction rule
prove(G>D):-
	select1(A|B,D,D1),
	prove(G>[A,B|D1]).

%Transformation according to left implication rule
prove(G>D):-
	select1(A=>B,G,G1),
	prove(G1>[A|D]),
	prove([B|G1]>D).

%Transformation according to right implication rule
prove(G>D):-
	select1(A=>B,D,D1),
	prove([A|G]>[B|D1]).

%Transformation according to left negation rule
prove(G>D):-
	select1(~A,G,G1),
	prove(G1>[A|D]).

%Transformation according to the right negation rule
prove(G>D):-
	select1(~A,D,D1),
	prove([A|G]>D1).