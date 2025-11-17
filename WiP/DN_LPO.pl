%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                          Copyright (C)2022 Joaquín Arias (URJC)
%  Name: DN_LPO.pl
%  Author: Joaquín Arias
%  Date: 22 October 2022
%  Purpose: Write First Order Lopic's Natural Deduction Proofs in LaTeX
%  LICENSE: Apache License 2.0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(_,_).

:- op(200, fy, ['\\forall', '\\exists']).
:- op(200, fy, '\\lnot').
:- op(300, xfy, ~~ ).
:- op(400, xfy,['\\land', '\\lor']).
:- op(600, xfy,['\\rightarrow', '\\leftrightarrow']).
:- op(600, xfy,['\\lnot', '\\forall', '\\exists']).


ej1 :-
    main([
        '\\lnot' ('\\forall' x ~~ '\\lnot' 'P'(x))
    ],
    '\\exists' x ~~ 'P'(x),
    [
        'Premisa'(1),
        'Supuesto'('\\lnot' ('\\exists' x ~~ 'P'(x))),
        'Supuesto'('P'(y)),
        'I' '\\exists' (3,y/x),
        'I' '\\land' (4,2),
        'I' '\\rightarrow' (3,5),
        'I' '\\lnot' (6),
        'I' '\\forall' (7,y/x),
        'I' '\\land' (8,1),
        'I' '\\rightarrow' (2,9),
        'I' '\\lnot' (10),
        'E' '\\lnot' (11)
        
    ]).

ej2 :-
    main([
        '\\forall' x ~~ ('P'(x) '\\rightarrow' 'Q'(x)),
        '\\forall' x ~~ ('R'(x) '\\rightarrow' 'Q'(x)),
        '\\forall' x ~~ ('P'(x) '\\lor' 'R'(x))
    ], '\\forall' x ~~ 'Q'(x),
        [
             'Premisa'(1),
             'Premisa'(2),
             'Premisa'(3),
             'E' '\\forall' (1,x/a),
             'E' '\\forall' (2,x/a),
             'E' '\\forall' (3,x/a),
             'E' '\\lor' (6,4,5),
             'I' '\\forall' (7,a/x)
        ]).

ej3 :-
    main([
        '\\exists' x ~~ 'P'(x)
    ],
        '\\lnot' ('\\forall' x ~~ '\\lnot' 'P'(x)),
        [
            'Premisa'(1),
            'E' '\\exists' (1,x/'a*'),
            'Supuesto'('\\forall' x ~~ '\\lnot' 'P'(x)),
            'E' '\\forall' (3,x/'a*'),
            'I' '\\land' (2,4),
            'I' '\\rightarrow' (3,5),
            'I' '\\lnot' (6)
        ]).


ej4 :-
    main([
        '\\forall' x ~~ ('P'(x) '\\rightarrow' 'Q'(x)),
        '\\exists' x ~~ 'P'(x)
    ],
        '\\exists' x ~~ 'Q'(x),
        [
             'Premisa'(1),
             'Premisa'(2),
             'E' '\\exists' (2,x/'a*'),
             'E' '\\forall' (1,x/'a*'),
             'E'  '\\rightarrow' (4,3),
             'I' '\\exists' (5,'a*'/x)
        ]).

pag204 :-
    main([
        '\\exists' x ~~ ('P'(x) '\\lor' 'Q'(x))
    ], '\\exists' x ~~ 'P'(x) '\\lor' '\\exists' x ~~ 'Q'(x),
        [
             'Premisa'(1),
             'E' '\\exists' (1,x/'a*'),
             'Supuesto'('P'('a*')),
             'I' '\\exists' (3,'a*'/x),
             'I' '\\lor' a(4,'\\exists' x ~~ 'Q'(x)),
             'I' '\\rightarrow' (3,5),
             'Supuesto'('Q'('a*')),
             'I' '\\exists' (7,'a*'/x),
             'I' '\\lor' b('\\exists' x ~~ 'P'(x),8),
             'I' '\\rightarrow' (7,9),
             'E' '\\lor' (2,6,10)
        ]).

pag205 :-
    main([
       '\\exists' x ~~ 'P'(x) '\\lor' '\\exists' x ~~ 'Q'(x)
    ],  '\\exists' x ~~ ('P'(x) '\\lor' 'Q'(x)),
        [
             'Premisa'(1),
             'Supuesto'('\\exists' x ~~ 'P'(x)),
             'E' '\\exists' (2,x/'a*'),
             'I' '\\lor' a(3,'Q'('a*')),
             'I' '\\exists' (4,'a*'/x),
             'I' '\\rightarrow' (2,5),
             'Supuesto'('\\exists' x ~~ 'Q'(x)),
             'E' '\\exists' (7,x/'a*'),
             'I' '\\lor' b('P'('a*'),8),
             'I' '\\exists' (9,'a*'/x),
             'I' '\\rightarrow' (7,10),
             'E' '\\lor' (1,6,11)
        ]).

pag214 :-
    main([],
         '\\lnot' ( '\\exists' x ~~ 'P'(x) ) '\\rightarrow' '\\forall' x ~~ '\\lnot' 'P'(x),
         [
             'Supuesto'('\\lnot' ('\\exists' x ~~ 'P'(x))),
             'Supuesto'('P'(y)),
             'I' '\\exists' (2,y/x),
             'I' '\\land' (3,1),
             'I' '\\rightarrow' (2,4),
             'I' '\\lnot' (5),
             'I' '\\forall' (6,y/x),
             'I' '\\rightarrow' (1,7)
         ]).


pag223 :-

    main([
        '\\forall' x ~~ ('P'(x) '\\rightarrow' 'Q'(x)),
        '\\forall' x ~~ ('P'(x) '\\land' 'R'(x) )
    ], '\\exists' x ~~ ( 'Q'(x) '\\land' 'R'(x) ),
        [
             'Premisa'(1),
             'Premisa'(2),
             'E' '\\forall' (1,x/a),
             'E' '\\forall' (2,x/a),
             'E' '\\land' a(4),
             'E' '\\land' b(4),
             'E' '\\rightarrow' (3,5),
             'I' '\\land' (7,6),
             'I' '\\exists' (8,a/x)
        ]).


pag233 :-
    main([
        '\\forall' x ~~ ('P'(x) '\\land' 'Q'(x) '\\rightarrow' 'R'(x)),
        '\\forall' x~~ ('P'(x) '\\land' 'Q'(x) '\\land' 'R'(x)'\\rightarrow' 'S'(x)),
        '\\exists' x ~~ ('S'(x) '\\land' 'P'(x) '\\rightarrow' 'T'(x))
    ],
        '\\exists' x ~~ ('P'(x) '\\land' 'Q'(x) '\\rightarrow' 'T'(x)),
        [
             'Premisa'(1),
             'Premisa'(2),
             'Premisa'(3),
             'E' '\\exists' (3,x/'a*'),
             'Supuesto'('P'('a*') '\\land' 'Q'('a*')),
             'E' '\\forall' (1,x/'a*'),
             'E' '\\land' a(5),
             'E' '\\land' b(5),
             'E' '\\rightarrow' (6,5),
             'I' '\\land' (8,9),
             'I' '\\land' (7,10),
             'E' '\\forall' (2,x/'a*'),
             'E' '\\rightarrow' (12,11),
             'I' '\\land' (13,7),
             'E' '\\rightarrow' (4,14),
             'I' '\\rightarrow' (5,15),
             'I' '\\exists' (16,'a*'/x)
             

        ]).

pag190 :-
    main([
        '\\forall' x ~~ 'R'(x)  '\\lor'  '\\forall' y ~~  '\\lnot' 'P'(y),
        '\\lnot'  ('\\exists' z ~~ ('P'(z)  '\\land'  'R'(z)))
    ],'\\forall' y ~~  '\\lnot' 'P'(y)
         ,[
             'Premisa'(1),
             'Premisa'(2),
             'Supuesto'('\\forall' y ~~ '\\lnot' 'P'(y)),
             'I' '\\rightarrow' (3,3),
             'Supuesto'('\\forall' x ~~ 'R'(x)),
             'Supuesto'('P'('a')),
             'E' '\\forall' (5,x/'a'),
             'I' '\\land' (6,7),
             'I' '\\exists' (8,'a'/z),
             'I' '\\land' (9,2),
             'I' '\\rightarrow' (6,10),
             'I' '\\lnot' (11),
             'I' '\\forall' (12,'a'/y),
             'I' '\\rightarrow' (5,13),
             'E' '\\lor' (1,14,4)
         ]).

kk:-
    parse([
        '∀x ~~ R(x) ∨ ∀y ~~ ¬P(y)',
        '¬∃z ~~ (P(z) ∧ R(z))'
    ], Premisa),
    parse([
        '∀y ~~ ¬P(y)'
    ], Deduccion),
    parse([
        '∃z ~~ (P(z) ∧ R(z))'
    ], [S1]),
    display(main(Premisa,Deduccion,S1)),nl.

parse([],[]).
parse([A|As],[B|Bs]) :-
    atom_codes(A,LA),
    display(LA),nl,
    parse_(LA,LB),
    atom_codes(B,LB),
    parse(As,Bs).
parse_([],[]).
%∧
parse_([226,136,167|As],
          [32,92,108,97,110,100,32|Bs]) :- !,
    parse_(As,Bs).
%∨
parse_([226,136,168|As],
          [32,92,108,111,114,32|Bs]) :- !,
    parse_(As,Bs).
%¬
parse_([194,172|As],
          [32,92,108,110,111,116,32|Bs]) :- !,
    parse_(As,Bs).
%→
parse_([226,134,146|As],
          [32,92,114,105,103,104,116,97,114,114,111,119,32|Bs]) :- !,
    parse_(As,Bs).
%↔
parse_([226,134,148|As],
          [32,92,108,101,102,116,114,105,103,104,116,97,114,114,111,119,32|Bs]) :- !,
    parse_(As,Bs).
%∃
parse_([226,136,131|As],
          [32,92,101,120,105,115,116,115,32|Bs]) :- !,
    parse_(As,Bs).
%∀
parse_([226,136,128|As],
          [92,102,111,114,97,108,108,32|Bs]) :- !,
    parse_(As,Bs).


parse_([A|As],[A|Bs]) :- parse_(As,Bs).


%% Ejemplos
ejemplo1 :-
    main([s '\\land' p '\\lor' q, p '\\rightarrow' '\\lnot' r, q '\\rightarrow' '\\lnot' r], s '\\land' '\\lnot' r, ['Premisa'(1), 'E' '\\land' b(1), 'Premisa'(2), 'Premisa'(3), 'E' '\\lor' (2,3,4), 'E' '\\land' a(1), 'I' '\\land' (6,5)]).

ejemplo2 :-
    main(['\\lnot'p '\\rightarrow' q '\\land' '\\lnot'q],p,['Premisa'(1),'I' '\\lnot' (1), 'E' '\\lnot' (2)]).

ejemplo3 :-
    main([p '\\rightarrow' '\\lnot'r,'\\lnot'r'\\rightarrow' q,p],q,['Premisa'(1),'Premisa'(3), 'E' '\\rightarrow' (1,2),'Premisa'(2), 'E' '\\rightarrow' (4,3)]).

ejemplo4 :-
    main([p '\\rightarrow' q,q'\\rightarrow' r],p'\\rightarrow' r, ['Premisa'(1),'Premisa'(2),'Supuesto'(p),'E' '\\rightarrow' (1,3),'E' '\\rightarrow' (2,4),'I' '\\rightarrow' (3,5)]).

ejemploMT :-
    main([r '\\rightarrow' (q '\\land' s), '\\lnot'(q '\\land' s)], '\\lnot'r, ['Premisa'(1), 'Premisa'(2), 'MT'(1,2)]).

ejemploSupuesto :- %% Falla porque no esta cerrado el supuesto :-)
    main([s '\\land' p '\\lor' q, p '\\rightarrow' '\\lnot' r, q '\\rightarrow' '\\lnot' r], s '\\land' '\\lnot' r, ['Premisa'(1), 'E' '\\land' b(1), 'Premisa'(2), 'Premisa'(3), 'Supuesto'(p1),'Supuesto'(p2),'Supuesto'(p3),'Supuesto'(p4),'Supuesto'(s '\\land' '\\lnot'r)]).

:- data counter/1, formula/2, tabular/1, cerrado/1, hay_supuesto/1, probar/1.
main(Premisas, Deduccion, ReglasInferencia) :-
   retractall(counter(_)), retractall(formula(_,_)), retractall(tabular(_)),retractall(cerrado(_)),retractall(hay_supuesto(_)),retractall(probar(_)),
    assert(counter(0)), assert(tabular(0)),
    format("\\item $ T~p  \\vdash  ~p $\n\n",[Premisas, Deduccion]),
    format("\n \\begin{enumerate}[leftmargin=1cm,rightmargin=2cm,nosep]\n",[]),
    eval(Premisas, Deduccion, ReglasInferencia),
    format("\n \\end{enumerate}",[]),
    probar_pendientes.

probar_pendientes :-
    setof(Nombre, probar(Nombre), Pendientes), !,
    probar_pendientes_(Pendientes).
probar_pendientes.

probar_pendientes_([]).
probar_pendientes_([Nombre|Ps]) :-
    retractall(counter(_)),retractall(formula(_,_)), retractall(tabular(_)),retractall(cerrado(_)),retractall(hay_supuesto(_)),
    assert(counter(0)), assert(tabular(0)),
    regla(Nombre, Premisas, Deduccion, Prueba), !,
    numbervars([Premisas,Deduccion,Prueba], 0, _),
    format("\n\n Prueba de la regla derivada ~p: $ T~p \\vdash  ~p $ \n\n",[Nombre,Premisas,Deduccion]),
    format("\n \\begin{enumerate}[leftmargin=1cm,rightmargin=2cm,nosep]\n",[]),
    eval(Premisas, Deduccion, Prueba), !,
    format("\n \\end{enumerate}",[]),
    probar_pendientes_(Ps).

eval(Premisas, Deduccion, [ R | ReglasInferencia ]) :-
    eval_regla(R,Premisas),
    eval(Premisas, Deduccion, ReglasInferencia).
eval(_,Deduccion,[]) :-
    check_deduccion(Deduccion).

'Premisa'(1,[P | _Premisas]) :- !,
    add_formula(P).
'Premisa'(A,[_ | Premisas]) :-
    A1 is A - 1,
    'Premisa'(A1,Premisas).

eval_regla(R,P):-
    (   exec(R,P) ->
        output(R)
    ;
        format("\nERROR aplicando\t\t~p",[R]), !, fail
    ).

exec('Premisa'(C),Premisas) :- !,
    'Premisa'(C,Premisas).
exec(Regla,_) :-
    Regla =.. [Nombre|Args],
    regla(Nombre,Premisas,Deduccion,_Prueba), !,
    assert(probar(Nombre)),
    exec_regla(Args,Premisas,Deduccion).
exec(Regla,_) :-
    catch(call(Regla),_,fail).


check_deduccion(Deduccion) :-
    retract(counter(C)),
    formula(C, Resultado),
    (   \+ hay_supuesto(_) ->
        (   Resultado = Deduccion ->
            %            format("~50|ok",[])
            true
        ;
            format("\nERROR: Resultado ~w no coincide con lo esperado ~w\n\n",[Resultado,Deduccion])
        )
    ;
        format("\nERROR: Supuesto no cerrado\n\n",[])
    ).

add_formula(Formula) :-
    next_couonter(C),
    asserta(formula(C,Formula)).

next_couonter(C1) :-
    retract(counter(C)),
    C1 is C + 1,
    asserta(counter(C1)).
    

output(Regla) :-
    format_regla(Regla,LRegla),
    tabular(T),
    counter(C),
    formula(C,Formula),
    format(" \\item[~p.] ",[C]),
    format_tabular(T),
    format("$ ~p $",[Formula]),
    format("~50|\\hspace{\\fill} ~p~p~p\n",LRegla).

:- use_module(library(formulae)).
:- use_module(library(terms)).
format_regla('Premisa'(_), ['Premisa','','']).
format_regla('Supuesto'(_), ['Supuesto','','']).
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\exists',Op,(Line,_)], atom_concat(['$',Op,'_{\\exists}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\exists',Op,(Line,_)], atom_concat(['$',Op,'_{\\exists}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\forall',Op,(Line,_)], atom_concat(['$',Op,'_{\\forall}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\forall',Op,(Line,_)], atom_concat(['$',Op,'_{\\forall}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\land','E',a(Line)], atom_concat(['$E_{\\land}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\land','E',b(Line)], atom_concat(['$E_{\\land}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\leftrightarrow','E',a(Line)], atom_concat(['$E_{\\leftrightarrow}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\leftrightarrow','E',b(Line)], atom_concat(['$E_{\\leftrightarrow}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\lor','I',a(Line,_)], atom_concat(['$I_{\\lor}('],LRule), !. 
format_regla(Rule, [LRule,(Line),')$']) :- Rule =.. ['\\lor','I',b(_,Line)], atom_concat(['$I_{\\lor}('],LRule), !. 
format_regla(Rule, [LRule,Conj,')$']) :- Rule =.. [Op,'I'|Arg], list_to_conj(Arg,Conj), atom_concat(['$I_{',Op,'}('],LRule). 
format_regla(Rule, [LRule,Conj,')$']) :- Rule =.. [Op,'E'|Arg], list_to_conj(Arg,Conj), atom_concat(['$E_{',Op,'}('],LRule). 
format_regla(Rule, [Rule,'','']) :- Rule =.. [Nombre|_], regla(Nombre,_,_,_).



format_tabular(0) :- !.
format_tabular(T) :-
    T1 is T - 1,
    format(" \\hspace{3em} ",[]),
    format_tabular(T1).


%% Reglas de inferencia
% Conjunción
'I' '\\land' (A,B) :-
    formula(A,FA),
    formula(B,FB),
    add_formula(FA '\\land' FB).

'E' '\\land' a(A) :-
    formula(A,FA '\\land' _FB),
    add_formula(FA).
'E' '\\land' b(A) :-
    formula(A,_FA '\\land' FB),
    add_formula(FB).
% Disyunción
'E' '\\lor' (A,B,C) :-
    formula(A,FB '\\lor' FC),
    formula(B,FB '\\rightarrow' F),
    formula(C,FC '\\rightarrow' F),
    add_formula(F).

'I' '\\lor' a(A,Formula) :-
    formula(A,FA),
    add_formula(FA '\\lor' Formula).
'I' '\\lor' b(Formula,B) :-
    formula(B,FB),
    add_formula(Formula '\\lor' FB).
% Negación
'I' '\\lnot' (A) :-
    formula(A, FA '\\rightarrow' B '\\land' '\\lnot' B),
    add_formula('\\lnot' FA).

'E' '\\lnot' (A) :-
    formula(A, '\\lnot' '\\lnot' FA),
    add_formula(FA).
% Implicación
'E' '\\rightarrow' (A,B) :-
    formula(A, FB '\\rightarrow' FC),
    formula(B, FB),
    add_formula(FC).
'I' '\\rightarrow' (A,B) :-
    hay_supuesto(A),
    formula(A,FA),
    valid(B),
    formula(B,FB),
    cierra(A),
    add_formula(FA '\\rightarrow' FB).
'Supuesto'(FA) :-
    increase_tab,
    add_formula(FA),
    counter(C),
    assert(hay_supuesto(C)).
% Doble implicación
'I' '\\leftrightarrow' (A,B) :-
    formula(A,FA '\\rightarrow' FB),
    formula(B,FB '\\rightarrow' FA),
    add_formula(FA '\\leftrightarrow' FB).
'E' '\\leftrightarrow' a(A) :-
        formula(A,FA '\\leftrightarrow' FB),
        add_formula(FA '\\rightarrow' FB).
'E' '\\leftrightarrow' b(A) :-
        formula(A,FA '\\leftrightarrow' FB),
        add_formula(FB '\\rightarrow' FA).

% Existe
'I' '\\exists' (A,Sust/Var) :-
    formula(A,FA),
    sustitute(FA,Sust/Var,FB),
    add_formula('\\exists' Var ~~ FB).
'E' '\\exists' (A, Var/Sust) :-
        formula(A,'\\exists' Var ~~ FA),
        sustitute(FA, Var/Sust, FB),
        add_formula(FB).
% Forall
'E' '\\forall' (A, Var/Sust) :-
        formula(A,'\\forall' Var ~~ FA),
        sustitute(FA, Var/Sust, FB),
        add_formula(FB).
'I' '\\forall' (A,Sust/Var) :-
    formula(A,FA),
    sustitute(FA,Sust/Var,FB),
    add_formula('\\forall' Var ~~ FB).

sustitute([],_,[]) :- !.
sustitute([A|As],S,[B|Bs]) :- 
    sustitute(A,S,B),
    sustitute(As,S,Bs), !.
sustitute(FA,S,FB) :-
    FA =.. [Op|Args],
    Args \= [], !,
    sustitute(Args,S,Brgs),
    FB =.. [Op|Brgs].
sustitute(A,A/B,B) :- !.
sustitute(A,_,A).
        

       
%% Predicados derivados
exec_regla(Args,Premisas,Deduccion) :-
    see_formulas(Args,Formulas),
    Premisas = Formulas,
    add_formula(Deduccion).
see_formulas([],[]).
see_formulas([A|As],[FA|FAs]) :-
    formula(A,FA),
    see_formulas(As,FAs).

regla('MT',[FA '\\rightarrow' FB,'\\lnot'FB],'\\lnot'FA,
      ['Premisa'(1),
       'Premisa'(2),
       'Supuesto'(FA),
       'E' '\\rightarrow' (1,3),
       'I' '\\land' (4,2),
       'I' '\\rightarrow' (3,5),    
       'I' '\\lnot' (6)
       ]).

    


valid(B) :-
    \+ cerrado(B).
cierra(A) :-
    counter(C),
    between(A,C,C1),
    assert(cerrado(C1)),
    fail.
cierra(A) :-
    decrease_tab,
    retract(hay_supuesto(A)).

increase_tab :-
    retract(tabular(Tab)),
    Tab1 is Tab + 1,
    assert(tabular(Tab1)).
decrease_tab :-
    retract(tabular(Tab)),
    Tab1 is Tab - 1,
    assert(tabular(Tab1)).
