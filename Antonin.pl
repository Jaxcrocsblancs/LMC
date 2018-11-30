:- op(20,xfy,?=). 

% Prédicats d'affichage fournis 

% set_echo: ce prédicat active l'affichage par le prédicat echo 
set_echo :- assert(echo_on). 

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo 
clr_echo :- retractall(echo_on). 

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T 
%          sinon, echo(T) réussit simplement en ne faisant rien. 

echo(T) :- echo_on, !, write(T). 
echo(_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Question%1%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
regle(F1?=F2,decompose):- functor(F1,N,A), functor(F2,N,A),!.

%regle clash test si les fonction on la même arité et si elles on le même nom
regle(F1?=F2,clash):- functor(F1,N,A),functor(F2,N,A),!.

%%%%Occur_Check%%%%

% on ne garde que les arguments de T et on test avec la récurrence que tout les éléments de R sont différents de X
% en effet il n'est pas possible de remonter un test vrai aux milieu d'autre test faux. Nous avons donc décidé de faire l'inverse 
% on test si tout les éléments sont différents et on retourne l'opposé. Si un argument est égaux à X un faux remonte dans notoccur_check
% pour finir par retourner vrai dans occur_check
occur_check(X,T):- T =.. [_|R], \+notoccur_check(X,R),!.
notoccur_check(X,[]).
notoccur_check(X,[T|R]):- X\==T, notoccur_check(X,R),!.
