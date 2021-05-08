:- use_module(library(gensym)).


refresh(_,[],[]) :- !.
refresh(C,[X|XS],[Xp|XSp]) :- refresh(C,X,Xp), refresh(C,XS,XSp), !.
refresh(C,_c,X) :- member([_c,X], C), !.
refresh(_,_c,_c) :- !.

assignVars([],[]).
assignVars([X|XS],[[X,_]|XSp]) :- assignVars(XS,XSp).

refreshCnst(C,X,Y) :- assignVars(C,Cp), refresh(Cp,X,Y).
% refreshCnst([1,2,3],[[1,4],[5,2],[1,2]],X), refreshCnst([1,2,3],[[4,4],[5,5],[1,2]],Y), X=Y.

refreshClause(CTX,[[_a,':',A],'->'|B],[Ap,'->'|Bp]) :- refresh([[_a,K]|CTX],A,Ap), refreshClause([[_a,K]|CTX],B,Bp),!.
refreshClause(CTX,A,Ap) :- refresh(CTX,A,Ap).
% refreshClause([],[[a,':',cA],'->',[b,':',[cB,a]],'->',[cC,b,a]],X).


initCls([_],[]).
initCls([X,'->'|XS],[X|ZS]) :- initCls(XS,ZS).

applyClause(C,G,CLS) :- refreshClause([],C,CLS), last(CLS,Cl), Cl=G.
% applyClause([[a,':',cA],'->',[b,':',[cB,a]],'->',[cC,b,a]],[K,k,l],CLS).

unas(X) :- not(not(X=unas)).

assignUnas(C,X) :- unas(X), X=C, !.
assignUnas(C,[X|_]) :- assignUnas(C,X).
assignUnas(C,[_|XS]) :- assignUnas(C,XS).
% T=[X,X,Y,Z,Y], assignUnas(1,T).

quoteWith([C|CS],T) :- assignUnas(C,T),!,quoteWith(CS,T).
quoteWith(_,_).
% T=[X,X,Y,Z,Y], quoteWith([1,2,3,4],T).
% T=[X,X,Y,Z,Y], quoteWith([1,2,3,4],T), refreshCnst([1,2,3,4],T,Tp).

replicateFor(_,[],[]).
replicateFor(C,[C|CS],[_|XS]) :- replicateFor(C,CS,XS). 

noSingletons([],[]).
noSingletons([[X]|XS],[X|ZS]) :- !, noSingletons(XS,ZS).
noSingletons([X|XS],[X|ZS]) :- noSingletons(XS,ZS),!.

proof(KB,[[K,':'|P],'->'|PS],[lambda,K,PRF]) :- !,proof([[K,':'|P]|KB],PS,PRF).
proof(KB,[P],PRF) :- !,proof(KB,P,PRF).
proof(KB,Goal,[Cn|REM]) :- member([Cn,':'|C],KB), applyClause(C,Goal,Cp),
  initCls(Cp,Cpi),
  replicateFor(KB,KBL,Cpi),
  maplist(proof,KBL,Cpi,REMp),
  noSingletons(REMp,REM).
  
/*
KB=[
  [p1,':',cA],
  [p3,':',cA],
  [p2,':',cB],
  [prf,':',[a,':',cA],'->',[b,':',cB],'->',[cC,b]]
  ],
proof(KB,[cC,K],PRF).

KB=[
  [prf,':',[a,':',cA],'->',[b,':',cB],'->',[cC,b]]
  ],
proof(KB,[[p1,':',cA],'->',[p2,':',cB],'->',[cC,K]],PRF).
*/
