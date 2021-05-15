:- use_module(solver).

exchange(X,Y,X,Y) :- !.
exchange(X,_,[lambda,X|E],[lambda,X|E]) :- !.
exchange(X,Y,[E1|E2],[E1p|E2p]) :- !, exchange(X,Y,E1,E1p), exchange(X,Y,E2,E2p).
exchange(_,_,E,E).

exchangeAll(CTX,X,Y) :- member([X,Y],CTX),!.
exchangeAll(CTX,[lambda,X|E],[lambda,X|Ep]) :- select([X,_],CTX,CTXp),!,exchangeAll(CTXp,E,Ep).
exchangeAll(CTX,[E1|E2],[E1p|E2p]) :- !, exchangeAll(CTX,E1,E1p), exchangeAll(CTX,E2,E2p).
exchangeAll(_,E,E).

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
evalStep([case,X,of,Cases],Res) :- !, eval(X,E),caseStm(E,[],Cases,Res).
evalStep([A|AS],[K|AS]) :- evalStep(A,K),!.
evalStep([A|AS],[A|KS]) :- evalStep(AS,KS).

%eval([[lambda,a,lambda,b,[a,b]],[lambda,a,a],k],R).

caseStm(E,CTX,[[lambda,X|Y]|R],T) :- !, caseStm(E,[[X,_]|CTX],[Y|R],T).
caseStm(E,CTX,[[K,'=',T]|_],Tp) :- exchangeAll(CTX,[K,'=',T],[Kp,'=',Tp]), E=Kp, !.
caseStm(E,_,[_|R],T) :- caseStm(E,[],R,T).


%Y-operator for recursion
fkt([N|ARGS],TRM,[[lambda,f,[ [lambda,g,[f,[g,g]]] , [lambda,g,[f,[g,g]]] ]],F]) :- fktp([N|ARGS],TRM,F).
fktp([],TRM,TRM).
fktp([ARG|ARGS],TRM,[lambda,ARG,R]) :- fktp(ARGS,TRM,R).

/*
fkt([concat,a,b],[case,a,of,[
  [mt,'=',b],
  [lambda,x,lambda,xs,[x,':',xs],'=',[x,':',[concat,xs,b]]]
  ] ],Concat),
eval([Concat,[q2,':',[q1,':',mt]],[q2,':',mt ]], Res).
eval([Concat,[q1,':',mt],[q2,':',mt] ], Res).
*/

/*
'HOU'(T1,T2,T1u) :- quote([T1,T2],[T1q,T2q]),
                      eval(T1q,T1e), eval(T2q,T2e),
                      unquote([T1e,T2e,T1q,T2q],[T1u,T2u,T1,T2]),
                      T1u = T2u.
                      */
/*
'HOU'([[lambda,a,a],[X,k,K,L]], [[lambda,a,a],[j,K,Y,M]], Res).
*/

/*
This didn't work because when etting two variables equal, they are always unified, but not with higher order unification. Therefore, only the above can really work...
*/
'HOU'(T1,T2,Res) :- quote([T1,T2],[T1q,T2q]),
                      eval(T1q,T1e), eval(T2q,T2e),
                      unquote([T1e,T2e,T1q,T2q],[T1u,T2u,T1,T2]),
                      shallowUnif(T1u,T2u,R),
                      ((R=true,!,Res=T1u) ; 'HOU'(T1u,T2u,Res)).

shallowUnif(X,Y,true) :- unas(X),X=Y,!.
shallowUnif(Y,X,true) :- unas(X),X=Y,!.
%TODO: check if this in correct in general...
shallowUnif([X|_],_,false) :- unas(X),!.
shallowUnif(_,[X|_],false) :- unas(X),!.
shallowUnif(X,X,true) :- !.
shallowUnif([X|XS],[Y|YS],R) :-
  maplist(shallowUnif,[X|XS],[Y|YS],L),
  and(L,R).

and([],true) :- !.
and([true|XS],R) :- !, and(XS,R).
and(_,false).
/*
'HOU'([[F,k],F], [[k,k],[lambda,a,[a,a]]], Res).
*/



%TODO: this is trying to prove the equivalence of two functions. Not sure if this can be done automatically in every possible case...
'HOE'(T1,T2) :- 'HOU'(T1,T2,_),!.
'HOE'([lambda,X1|E1],[lambda,X2|E2]) :- pseudoQuote(K),
  eval([[lambda,X1|E1],K], E1p),
  eval([[lambda,X2|E2],K], E2p),
  'HOE'(E1p,E2p).

/*
'HOE'([lambda,x,x],[lambda,y,y]).
*/










%
