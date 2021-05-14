exchange(X,Y,X,Y) :- !.
exchange(X,_,[lambda,X|E],[lambda,X|E]) :- !.
exchange(X,Y,[E1|E2],[E1p|E2p]) :- !, exchange(X,Y,E1,E1p), exchange(X,Y,E2,E2p).
exchange(_,_,E,E).

removeSingleBrackets([],[]).
removeSingleBrackets([[X]|XS],RS) :- !,removeSingleBrackets([X|XS],RS).
removeSingleBrackets([[X|Xxs]|XS],[[Xp|Xpxs]|RS]) :- !, removeSingleBrackets([X|Xxs],[Xp|Xpxs]), removeSingleBrackets(XS,RS).
removeSingleBrackets([S|XS],[S|RS]) :- removeSingleBrackets(XS,RS).

eval(E,F) :- evalStep(E,K),!,eval(K,F).
eval(R,R).

evalStep([E],R) :- !, evalStep(E,R).
evalStep([[lambda,X|E],Y|R], [Ep|R]) :- !, exchange(X,Y,E,Ep).
%TODO: WARNING: this is not lazy!
evalStep([case,X,of,Cases],Res) :- !, eval(X,E), caseStm(E,Cases,Res).
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
  [[X,':'|XS],'=',[X,':',[concat,XS,b]]]
  ] ],Concat),
eval([Concat,[q1,':',[]],[q2,':',[]] ], Res).
*/














%
