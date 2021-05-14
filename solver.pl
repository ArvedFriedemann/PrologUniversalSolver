:- module(solver,[quote/1,unquote/2]).
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

unas(X) :- not(not(X=unas)).

assignUnas(C,X) :- unas(X), X=C, !.
assignUnas(C,[X|_]) :- assignUnas(C,X).
assignUnas(C,[_|XS]) :- assignUnas(C,XS).
% T=[X,X,Y,Z,Y], assignUnas(1,T).

quoteWith([C|CS],T) :- assignUnas(C,T),!,quoteWith(CS,T).
quoteWith(_,_).
% T=[X,X,Y,Z,Y], quoteWith([1,2,3,4],T).
% T=[X,X,Y,Z,Y], quoteWith([1,2,3,4],T), refreshCnst([1,2,3,4],T,Tp).
quote(T) :- gensym(q,C), assignUnas(var(C),T),!,quote(T).
quote(_).
% T=[X,X,Y,Z,Y], quote(T).
vars(T,VS) :- flatten(T,TF), flatvars(TF,VS).
flatvars([],[]).
flatvars([var(X)|XS],[var(X)|ZS]) :- !,flatvars(XS,ZS).
flatvars([_|XS],ZS) :- !,flatvars(XS,ZS).

unquote(T,U) :- vars(T,V), refreshCnst(V,T,U).
% T=[X,X,Y,Z,Y], quote(T), unquote(T,U).

replicateFor(_,[],[]).
replicateFor(C,[C|CS],[_|XS]) :- replicateFor(C,CS,XS).

replicateZip(_,[],[]).
replicateZip(C,[X|XS],[[C,X]|ZS]) :- replicateZip(C,XS,ZS).

noSingletons([],[]).
noSingletons([[X]|XS],[X|ZS]) :- !, noSingletons(XS,ZS).
noSingletons([X|XS],[X|ZS]) :- noSingletons(XS,ZS),!.
/*
proof(KB,[P,':',Goal],P) :- !,proof(KB,Goal,P).
proof(KB,[[K,':'|P],'->'|PS],[lambda,K,PRF]) :- !,proof([[K,':'|P]|KB],PS,PRF).
proof(KB,[P],PRF) :- !,proof(KB,P,PRF).
proof(KB,Goal,[Cn|REM]) :- member([Cn,':'|C],KB), applyClause(C,Goal,Cp),
  initCls(Cp,Cpi),
  replicateFor(KB,KBL,Cpi),
  maplist(proof,KBL,Cpi,REMp),
  noSingletons(REMp,REM).
*/

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
/*
%assumes clause result still carries proof!
%proofStep(KB,_,[]) :- member([_,':',bot],KB). %should not be needed
proofStep(KB,[[_c,':',C],'->'|CS], [lambda,_c,P],[[ [[_c,':',C]|KB],[P,':'|CS] ]]).
proofStep(KB,Goal,[case,N,SubPrf],KBGoals) :- %TODO: make the next goals be implications
  select([N,':'|C],KB,KBpp),
  refresh([[N,K]],KBpp,KBp),
  refresh([[N,K]],Goal,Goalp),
  refresh([[N,K]],C,Cp),
  findall([KBp,[[of,K,'=',PRF],':'|SUB],PRF],
      (member([K,':'|X],KBp),
       applyClause(X,Cp,SUBp),
       append([SUBp,['->',Goalp]],SUB))
    ,KBGoals),
  proofsOfKBGoals(KBGoals,SubPrf).
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
%WARNING: is a list of goals
proofAndorraFin(KBGoals,R) :-
  select(Goal,KBGoals,KBGoalsP),
  aggregate_all(count,proofStep(Goal,_),1), !,
  proofStep(Goal,Steps),
  append([Steps,KBGoalsP],Next),
  proofAndorraFin(Next,R).
proofAndorraFin(R,R).



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
