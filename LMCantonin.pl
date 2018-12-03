% ================Ressources donn�es avec le sujet=====================

:- op(20,xfy,?=).

% Pr�dicats d'affichage fournis

% set_echo: ce pr�dicat active l'affichage par le pr�dicat echo
set_echo :- assert(echo_on).

% clr_echo: ce pr�dicat inhibe l'affichage par le pr�dicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionn�, echo(T) affiche le terme T
%          sinon, echo(T) r�ussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).

% =============================Question=1===============================


% regle(E,R) : d�termine la r�gle de transformation R qui s�applique �
% l��quation E, par exemple, le
% but ?- regle(f(a) ?= f(b),decompose) r�ussit.
% � occur_check(V,T) : teste si la variable V appara�t dans le terme T.
% � reduit(R,E,P,Q) : transforme le syst�me d��quations P en le syst�me
% d��quations Q par applicationde la r�gle de transformation R � l��quation E.

%Documentation sur les commandes prolog
%http://www.swi-prolog.org/pldoc/
%
%%%%Regle%%%%%

%regle rename qui test si les deux parametre sont des variables (coupe � la fin pour reduire l'arbre).
regle(X?=T,rename):- var(X),var(T).

%regle simplify qui test que le permier param�tre est une variable et le second une constante (coupe � la fin pour reduire l'arbre)
regle(X?=T,simplify):- var(X),atomic(T).

%regle expand qui test si X est une variable et que T est compos� mais ne poss�de pas X dans ses arguments
regle(X?=T,expand):- var(X),compound(T),\+occur_check(X,T),!.

%regle check qui test si X est diff�rents de T et que X apparait dans T
regle(X?=T,check):- X\==T,occur_check(X,T),!.

%regle orient qui test si T n'est pas une variable
regle(T?=X,orient):- \+var(T),var(X),!.

%regle decompose retourne vrai si F1 et F2 sont deux fonctions avec le m�me nom et avec la m�me arit�
regle(F1?=F2,decompose):-  compound(F1), compound(F2), functor(F1,N,A), functor(F2,N,A),!.

%regle clash test si les fonction on la m�me arit� et si elles on le m�me nom
regle(F1?=F2,clash):-  compound(F1), compound(F2), functor(F1,N,A),functor(F2,N,A),!.

%%%%Occur_Check%%%%

% on ne garde que les arguments de T et on test avec la r�currence que tout les �l�ments de R sont diff�rents de X
% en effet il n'est pas possible de remonter un test vrai aux milieu d'autre test faux. Nous avons donc d�cid� de faire l'inverse
% on test si tout les �l�ments sont diff�rents et on retourne l'oppos�. Si un argument est �gaux � X un faux remonte dans notoccur_check
% pour finir par retourner vrai dans occur_check
occur_check(X,T):- T =.. [_|R], \+notoccur_check(X,R),!.
notoccur_check(_X,[]).
notoccur_check(X,[T|R]):- X\==T, notoccur_check(X,R),!.


%%%%%Reduit%%%%%%
reduit(rename,X?=T,[X?=T|R],R):- X=T,!.
reduit(simplify,X?=T,[X?=T|R],R) :- regle(X?=T,simplify),X=T,!.
reduit(expand,X?=T,[X?=T|R],R):- regle(X?=T,expand),X=T,!.
reduit(orient,X?=T,[X?=T|R],[T?=X|R]):- regle(X?=T,orient),!.
reduit(decompose,X?=T,[X?=T|Q],R):-
    regle(X?=T,decompose),
    X=..[_|LX], T=..[_|LT],
    decomposeEnEquation(LX,LT,P),
    append(P,Q,R),!.

decomposeEnEquation([TX|LX],[TT|LT],[TX?=TT|R]):-decomposeEnEquation(LX,LT,R),! .
decomposeEnEquation([],[],[]).



%%%%%Unifie%%%%%%
unifie([[]]):-!.
unifie([]):-!.

unifie([X?=T|Rest]):-
    writeln([X?=T|Rest]),
    regle(X?=T,rename),!,
     writeln("rename "),
    reduit(rename,X?=T,[X?=T|R],R),
	unifie(Rest),!.

unifie([X?=T|Rest]):-
    regle(X?=T,simplify),!,
	writeln("simplify "),
    reduit(simplify,X?=T,[X?=T|R],R),
	unifie(Rest),!.

unifie([X?=T|Rest]):-
    regle(X?=T,expand),!,
    writeln("expand "),
    reduit(expand,X?=T,[X?=T|R],R),
	unifie(Rest),!.

unifie([X?=T|R]):-
    regle(X?=T,orient),!,
	writeln("orient "),
    reduit(orient,X?=T,[X?=T|R],Q),
	unifie(Q),!.

unifie([X?=T|Rest]):-
    regle(X?=T,decompose),!,
    writeln("decompose "),
    reduit(decompose,X?=T,[X?=T|Rest],R),
	unifie(R),!.

unifie([X?=T|Rest]):-
    atomic(X),atomic(T),X==T,
    writeln("atomic "),
	unifie(Rest),!.

unifie([X?=T|_Rest]):-
    regle(X?=T,check),
    writeln("check"),
    fail.

unifie([X?=T|_Rest]):-
    regle(X?=T,clash),
    writeln("clash"),
    fail.
