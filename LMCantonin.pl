% ================Ressources données avec le sujet=====================

:- op(20,xfy,?=).

% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :-  !, write(T).
echo(_).

% =============================Question=1===============================


% regle(E,R) : détermine la règle de transformation R qui s’applique à
% l’équation E, par exemple, le
% but ?- regle(f(a) ?= f(b),decompose) réussit.
% — occur_check(V,T) : teste si la variable V apparaît dans le terme T.
% — reduit(R,E,P,Q) : transforme le système d’équations P en le système
% d’équations Q par applicationde la règle de transformation R à l’équation E.

%Documentation sur les commandes prolog
%http://www.swi-prolog.org/pldoc/
%
%%%%Regle%%%%%

%regle rename qui test si les deux parametre sont des variables (coupe à la fin pour reduire l'arbre).
regle(X?=T,rename):- var(X),var(T).

%regle simplify qui test que le permier paramètre est une variable et le second une constante (coupe à la fin pour reduire l'arbre)
regle(X?=T,simplify):- var(X),atomic(T).

%regle expand qui test si X est une variable et que T est composé mais ne posséde pas X dans ses arguments
regle(X?=T,expand):- var(X),compound(T),\+occur_check(X,T),!.

%regle check qui test si X est différents de T et que X apparait dans T
regle(X?=T,check):- X\==T,occur_check(X,T),!.

%regle orient qui test si T n'est pas une variable
regle(T?=X,orient):- \+var(T),var(X),!.

%regle decompose retourne vrai si F1 et F2 sont deux fonctions avec le même nom et avec la même arité
regle(F1?=F2,decompose):-  compound(F1), compound(F2), functor(F1,N,A), functor(F2,N,A),!.

%regle clash test si les fonction on la même arité et si elles on le même nom
regle(F1?=F2,clash):-  compound(F1), compound(F2), functor(F1,N,A)\=functor(F2,N,A),!.

%%%%Occur_Check%%%%

% on ne garde que les arguments de T et on test avec la récurrence que tout les éléments de R sont différents de X
% en effet il n'est pas possible de remonter un test vrai aux milieu d'autre test faux. Nous avons donc décidé de faire l'inverse
% on test si tout les éléments sont différents et on retourne l'opposé. Si un argument est égaux à X un faux remonte dans notoccur_check
% pour finir par retourner vrai dans occur_check
occur_check(X,T):- T =.. [_|R], \+notoccur_check(X,R),!.
notoccur_check(_X,[]).
notoccur_check(X,[T|R]):- X\==T, notoccur_check(X,R),!.


%%%%%Reduit%%%%%%
reduit(rename,X?=T,[X?=T|R],R):- X=T,!.
reduit(simplify,X?=T,[X?=T|R],R) :- X=T,!.
reduit(expand,X?=T,[X?=T|R],R):-X=T,!.
reduit(orient,X?=T,[X?=T|R],[T?=X|R]):- !.
reduit(decompose,X?=T,[X?=T|Q],R):-
    X=..[_|LX], T=..[_|LT],
    decomposeEnEquation(LX,LT,P),
    append(P,Q,R),!.

decomposeEnEquation([TX|LX],[TT|LT],[TX?=TT|R]):-decomposeEnEquation(LX,LT,R),! .
decomposeEnEquation([],[],[]).



%%%%%Unifie%%%%%%
unifie([]):-!.

unifie([X?=T|Rest]):-
    atomic(X),atomic(T),X==T,
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('atomic:    '),echo(X?=T),nl,
	unifie(Rest),!.

unifie([X?=T|Rest]):-
    regle(X?=T,rename),!,
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('rename:    '),echo(X?=T),nl,
    reduit(rename,X?=T,[X?=T|R],R),
	unifie(Rest),!.

unifie([X?=T|Rest]):-
    regle(X?=T,simplify),!,
	echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('simplify:    '),echo(X?=T),nl,
    reduit(simplify,X?=T,[X?=T|R],R),
	unifie(Rest),!.

unifie([X?=T|Rest]):-
    regle(X?=T,expand),!,
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('expand:    '),echo(X?=T),nl,
    reduit(expand,X?=T,[X?=T|R],R),
	unifie(Rest),!.

unifie([X?=T|Rest]):-
    regle(X?=T,orient),!,
	echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('orient:    '),echo(X?=T),nl,
    reduit(orient,X?=T,[X?=T|Rest],Q),
	unifie(Q),!.

unifie([X?=T|Rest]):-
    regle(X?=T,decompose),!,
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('decompose:    '),echo(X?=T),nl,
    reduit(decompose,X?=T,[X?=T|Rest],R),
	unifie(R),!.

unifie([X?=T|Rest]):-
    regle(X?=T,check),
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('check:    '),echo(X?=T),nl,
    fail.

unifie([X?=T|Rest]):-
    regle(X?=T,clash),
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('clash:    '),echo(X?=T),nl,
    fail.
% =============================Question=2===============================

unifie([],_) :- !.

unifie(P,choix_premier):- choix_premier(P,_,_,_),!.

unifie(P,choix_pondere) :- choix_pondere(P,_,_,clash),!.
choix_premier(P,_,_,_):- unifie(P),!.


choix_pondere([],_,_,_).  

choix_pondere([X?=T|Rest],_,_,X):-
    atomic(X),atomic(T),X==T,
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('atomic:    '),echo(X?=T),nl,
	choix_pondere(Rest,_,_,X),!.

choix_pondere([X?=T|Rest],_,_,clashcheck):-
    regle(X?=T,clash),
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('clash:    '),echo(X?=T),nl,
    fail.

choix_pondere([X?=T|Rest],_,_,clashcheck):-
	regle(X?=T,check),
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('check:    '),echo(X?=T),nl,
    fail.

choix_pondere([X?=T|_P],[X?=T|_Q],_,clashcheck):-!.
choix_pondere([],Q,_,clashcheck):-
    choix_pondere(Q,_,_,renamesimplify),!.   

choix_pondere([X?=T|Rest],_,_,renamesimplify):-
    regle(X?=T,rename),!,
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('rename:    '),echo(X?=T),nl,
    reduit(rename,X?=T,[X?=T|R],R),
    choix_pondere(Rest,_,_,renamesimplify).

choix_pondere([X?=T|Rest],_,_,renamesimplify):-
    regle(X?=T,simplify),!,
    echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('simplify:    '),echo(X?=T),nl,
    reduit(simplify,X?=T,[X?=T|R],R),
    choix_pondere(Rest,_,_,renamesimplify). 

choix_pondere([X?=T|_P],[X?=T|_Q],_,renamesimplify):-!.
choix_pondere([],Q,_,renamesimplify):-
    choix_pondere(Q,_,_,orient),!.

choix_pondere([X?=T|Rest],_,_,orient):-
   regle(X?=T,orient),!,
	echo('systeme:  '),echo([X?=T|Rest]),nl,
    echo('orient:    '),echo(X?=T),nl,
    reduit(orient,X?=T,[X?=T|Rest],Q),
    choix_pondere(Q,_,_,orient). 

choix_pondere([X?=T|_P],[X?=T|_Q],_,orient):-!.
choix_pondere([],Q,_,orient):-
    choix_pondere(Q,_,_,orient),!.


% =============================Question=3===============================
% N'affiche pas la trace d'execution
unif(P) :-
  clr_echo,unifie(P).

% affiche la trace d'execution
trace_unif(P) :- 
  set_echo,unifie(P).
