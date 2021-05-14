:- use_module(solver).

exchange(X,Y,X,Y) :- !.
exchange(X,_,[lambda,X|E],[lambda,X|E]) :- !.
exchange(X,Y,[E1|E2],[E1p|E2p]) :- !, exchange(X,Y,E1,E1p), exchange(X,Y,E2,E2p).
exchange(_,_,E,E).


removeSingleBrackets([X],Xp) :- !,removeSingleBrackets(X,Xp).
removeSingleBrackets([X|XS],Xp) :- !,removeSingleBracketsp([X|XS],Xp).
removeSingleBrackets(X,X).

removeSingleBracketsp([],[]).
removeSingleBracketsp([[X]|XS],RS) :- !,removeSingleBracketsp([X|XS],RS).
removeSingleBracketsp([[X|Xxs]|XS],[[Xp|Xpxs]|RS]) :- !, removeSingleBracketsp([X|Xxs],[Xp|Xpxs]), removeSingleBracketsp(XS,RS).
removeSingleBracketsp([S|XS],[S|RS]) :- !,removeSingleBracketsp(XS,RS).
%removeSingleBrackets([[[a]],[[b],c]],R).

eval(E,F) :- removeSingleBrackets(E,Eb), evalStep(Eb,K),!,removeSingleBrackets(K,Kb),eval(Kb,F).
eval(R,Rb) :- removeSingleBrackets(R,Rb).

evalStep([[lambda,X|E],Y|R], [Ep|R]) :- !, exchange(X,Y,E,Ep).
%TODO: WARNING: this is not lazy!
evalStep([case,X,of,Cases],Res) :- !, eval(X,E), unquote(Cases,CasesQ),caseStm(E,CasesQ,Res).
evalStep([A|AS],[K|AS]) :- evalStep(A,K),!.
evalStep([A|AS],[A|KS]) :- evalStep(AS,KS).

%eval([[lambda,a,lambda,b,[a,b]],[lambda,a,a],k],R).

caseStm(E,[[E,'=',T]|_],T) :- !. %TODO: unquote!
caseStm(E,[_|R],T) :- caseStm(E,R,T).

%Y-operator for recursion
fkt([N|ARGS],TRM,[[lambda,f,[ [lambda,g,[f,[g,g]]] , [lambda,g,[f,[g,g]]] ]],F]) :- fktp([N|ARGS],TRM,F).
fktp([],TRM,TRM).
fktp([ARG|ARGS],TRM,[lambda,ARG,R]) :- fktp(ARGS,TRM,R).

/*
fkt([concat,a,b],[case,a,of,[
  [[],'=',b],
  [[var(x),':',var(xs)],'=',[var(x),':',[concat,var(xs),b]]]
  ] ],Concat),
eval([Concat,[q1,':',[]],[q2,':',[]] ], Res).
*/














%
