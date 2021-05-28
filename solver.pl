:- module(solver,[pseudoQuote/1,quote/2,unquote/2,unquoteOrig/3,unas/1,assig/1,refreshClause/3]).
:- use_module(library(gensym)).


refresh(_,[],[]) :- !.
refresh(C,[X|XS],[Xp|XSp]) :- refresh(C,X,Xp), refresh(C,XS,XSp), !.
refresh(C,_c,X) :- member([_c,X], C), !.
refresh(_,_c,_c) :- !.

assignVars([],[]).
assignVars([X|XS],[[X,_]|XSp]) :- assignVars(XS,XSp).

refreshCnst(C,X,Y) :- assignVars(C,Cp), refresh(Cp,X,Y).
% refreshCnst([1,2,3],[[1,4],[5,2],[1,2]],X), refreshCnst([1,2,3],[[4,4],[5,5],[1,2]],Y), X=Y.

refreshClause(CTX,[[_a,':',A],'->'|B],[[K,':',Ap],'->'|Bp]) :-
  refresh([[_a,K]|CTX],A,Ap), refreshClause([[_a,K]|CTX],B,Bp),!.
refreshClause(CTX,A,Ap) :- refresh(CTX,A,Ap).
% refreshClause([],[[a,':',cA],'->',[b,':',[cB,a]],'->',[cC,b,a]],X).


initCls([_],[]).
initCls([X,'->'|XS],[X|ZS]) :- initCls(XS,ZS).

proofVars([],[]).
proofVars([[P,':',_],'->'|XS],[P|ZS]) :- proofVars(XS,ZS).

%TODO: last is a hack. Won't work for functions
applyClause(C,[G],CLS) :- !, applyClause(C,G,CLS).
applyClause(C,G,CLS) :- refreshClause([],C,CLS), last(CLS,Cl), Cl=G.
% applyClause([[a,':',cA],'->',[b,':',[cB,a]],'->',[cC,b,a]],[K,k,l],CLS).

assig(X) :- nonvar(X).% atom(X) ; compound(X).
unas(X) :- not(assig(X)).% not(not(X=unas)).

assignUnas(C,X) :- unas(X), X=C, !.
assignUnas(C,[X|_]) :- assignUnas(C,X).
assignUnas(C,[_|XS]) :- assignUnas(C,XS).
% T=[X,X,Y,Z,Y], assignUnas(1,T).

quoteWith([C|CS],T) :- assignUnas(C,T),!,quoteWith(CS,T).
quoteWith(_,_).
% T=[X,X,Y,Z,Y], quoteWith([1,2,3,4],T).
% T=[X,X,Y,Z,Y], quoteWith([1,2,3,4],T), refreshCnst([1,2,3,4],T,Tp).
pseudoQuote(T) :- gensym(q,C), assignUnas(var(C),T),!,pseudoQuote(T).
pseudoQuote(_).
% T=[X,X,Y,Z,Y], pseudoQuote(T).
vars(T,VS) :- flatten(T,TF), flatvars(TF,VS).
flatvars([],[]).
flatvars([var(X)|XS],[var(X)|ZS]) :- !,flatvars(XS,ZS).
flatvars([_|XS],ZS) :- !,flatvars(XS,ZS).

unquote(T,U) :- vars(T,V), refreshCnst(V,T,U).
% T=[X,X,Y,Z,Y], pseudoQuote(T), unquote(T,U).
unquoteOrig(T,O,O) :- unquote(T,O).

quote(T,Tp) :- findall(T,pseudoQuote(T),[Tp]).
%K = [[X,Y],k,Y], quote(K,Tp), unquoteOrig(Tp,K,Uq).




replicateFor(_,[],[]).
replicateFor(C,[C|CS],[_|XS]) :- replicateFor(C,CS,XS).

replicateZip(_,[],[]).
replicateZip(C,[X|XS],[[C,X]|ZS]) :- replicateZip(C,XS,ZS).

noSingletons([],[]).
noSingletons([[X]|XS],[X|ZS]) :- !, noSingletons(XS,ZS).
noSingletons([X|XS],[X|ZS]) :- noSingletons(XS,ZS),!.

/*
proofGen(SolveKB,GS,RES) :-
  proofAndorraFin(GS,GSF),
  quote(GSF),
  unquote(GSF,GSU),
  ((GSF= [],
    %forall(member([_,_,PRF],KBGoals), vars(PRF,[])),
    RES = GS, !) %TODO: WARNING: andorra removes proven goals and with it the assigned variables. As they are not in the original goal anymore, this could cause problems.
    ;
  ( quote(SolveKB),
    unquote(SolveKB,SolveKBU),
    proofAndorraFin([[SolveKBU,[solve,[SolveKB,GSF],[SolveKBp,GSFp]],_]],Next),
    quote(SolveKBp),quote(GSFp), %Need to be quoted again (new variables)
    unquote(KBp,KBpU),unquote(Gp,GpU),unquote(Pp,PpU),
    ((vars(Pp,[]),
      RES = [KBpU,GpU,PpU], !)
      ;
      proofGen([KBpU,GpU,PpU],RES)) )).
*/


/*
KB=[
  [p1,':',cA],
  [p3,':',cB],
  [p2,':',cB],
  [prf,':',[a,':',cA],'->',[b,':',cB],'->',[cC,b]]
  ],
proof(KB,[cC,K],PRF).

KB=[
  [prf,':',[a,':',cA],'->',[b,':',cB],'->',[cC,b]]
  ],
proof(KB,[[p1,':',cA],'->',[p2,':',cB],'->',[cC,K]],PRF).

KB=[
  [p1,':',cA],
  [p2,':',cB],
  [prf,':',[a,':',cA],'->',[b,':',cB],'->',[cC,b]]
  ],
proofGen([KB,[cC,K],PRF],RES).
*/

proofStep([KB,[G],P],KBGoals) :- !, proofStep([KB,G,P],KBGoals).
%proofStep([_,set,_],[]).
proofStep([KB,[[_c,':',C],'->'|CS], [lambda,_c,P]],[[ [[_c,':',C]|KB],CS,P ]]) :- !.
proofStep([KB,Goal,[FKT|ARGS]],KBGoals) :-
  member([FKT,':'|C],KB),
  applyClause(C,Goal,Cp),
  initCls(Cp,Goals),
  mapProofVars(Goals,ARGS),
  kbZip(KB,Goals,KBGoals).

%[KB,Goal,PRF]
proof(STM) :-
  proofStep(STM,States),
  maplist(proof,States).

proofAndorra(KBGoals):- proofAndorraFin(KBGoals,_).
%[[KB,Goal,PRF]]
proofAndorraFin(KBGoals,R) :-
  select(Goal,KBGoals,KBGoalsP),
  aggregate_all(count,proofStep(Goal,_),1), !,
  proofStep(Goal,Steps),
  append([Steps,KBGoalsP],Next),
  proofAndorraFin(Next,R).
proofAndorraFin(R,R).

%[[KB,Goal,PRF]]
proofFixSolveKB(SolveKB,KBGoals) :-
  proofAndorraFin(KBGoals, KBGoalsP),
  ((KBGoals = [], !) ; (
  quote(KBGoalsP,KBGoalsQ),
  proofFixSolveKB([[SolveKB,[solve, KBGoalsQ],_]|KBGoalsP])
  %TODO: additionally stop when original proof is fully applied
  %TODO: unquoting? prolly needs to be done manually here...
  )




kbZip(_,[],[]).
kbZip(KB,[[P,':'|G]|XS],[[KB,G,P]|ZS]) :- kbZip(KB,XS,ZS).

proofsOfKBGoals([],[]).
proofsOfKBGoals([[_,[P,':'|_]]|XS],[P|ZS]) :- proofsOfKBGoals(XS,ZS).

kbGoalsToGoals([],[]).
kbGoalsToGoals([[_,G,_]|XS],[G|ZS]) :- kbGoalsToGoals(XS,ZS).

mapProofVars([],[]).
mapProofVars([[P,':'|_]|XS],[P|ZS]):- mapProofVars(XS,ZS).


%dataDeclToFkt([data,[':'|T],where],[])
/*
KB = [ [a,':',cA]
      ,[f,':',[ap,':',cA],'->',cB]
      ],
proofStep(KB,cB,PRF,PS), kbGoalsToGoals(PS,P).

KB = [ [f,':',[ap,':',cA],'->',cB]
      ],
proofStep(KB,[[a,':',cA],'->',cB],PRF,PS), kbGoalsToGoals(PS,P).

KB = [ [f,':',[ap,':',cA],'->',cB]
      ],
proof([KB,[[a,':',cA],'->',cB],PRF]).

KB = [ [f,':',[ap,':',cA],'->',cB]
      ],
proofAndorra([[KB,[[a,':',cA],'->',cB],PRF]]).

KB = [ [a,':',cA]
      ,[p1,':',cA]
      ,[p2,':',cA]
      ],
proofAndorra([[KB,cA,PRF]]).


KB = [ [a,':',cA]
      ,[p1,':',cA]
      ,[p2,':',cA]
      ],
proofStep(KB,cA,[case,a,PRF],PS), kbGoalsToGoals(PS,P).


KB = [ [left,':',[a,':',cA],'->',[cA,v,cB]]
      ,[right,':',[a,':',cA],'->',[cA,v,cB]]
      ,[ab,':',[cB,v,cA]]
      ],
proofStep(KB,[cA,v,cB],PRF,PS), kbGoalsToGoals(PS,P).
*/










%
