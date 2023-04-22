%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                          Copyright (C)2023 Joaquín Arias (URJC)
%  Name: DeduccionNatural.pl
%  Author: Joaquín Arias
%  Date: 22 April 2023
%  Purpose: Execute Natural Deduction Proofs
%  LICENSE: Apache License 2.0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module('DeduccionNatural',_).

% Operator precedence
:- op(200, fy, !).
:- op(400, xfy,[and, or]).
:- op(600, xfy,[-->, <->]).

% Auxiliary precedence for !
% Used to define the inference rules
:- op(400, xfy, !).

%% Examples
ejemplo1 :-
    main([ s and p or q, p --> ! r, q --> ! r ],
         s and ! r,
         [ 'Premisa'(1),
           'E' and b(1),
           'Premisa'(2),
           'Premisa'(3),
           'E' or (2, 3, 4),
           'E' and a(1),
           'I' and (6, 5)
         ]).

ejemplo2 :-
    main([ !p --> q and !q ],
         p,
         [ 'Premisa'(1),
           'I' ! (1),
           'E' ! (2)
         ]).

ejemplo3 :-
    main([ p --> !r, !r-->q, p ],
         q,
         [ 'Premisa'(1),
           'Premisa'(3),
           'E' --> (1, 2),
           'Premisa'(2),
           'E' --> (4, 3)
         ]).

ejemplo4 :-
    main([ p --> q, q-->r ],
         p-->r,
         [ 'Premisa'(1),
           'Premisa'(2),
           'Supuesto'(p),
           'E' --> (1, 3),
           'E' --> (2, 4),
           'I' --> (3, 5)
         ]).

ejemploMT :-
    main([ r --> (q and s), !(q and s) ],
         !r,
         [ 'Premisa'(1),
           'Premisa'(2),
           'MT'(1, 2)
         ]).

%% This example fails becuase the assumption is not closed
ejemploSupuesto :- 
    main( [ s and p or q, p --> ! r, q --> ! r ],
          s and ! r,
          [ 'Premisa'(1),
            'E' and b(1),
            'Premisa'(2),
            'Premisa'(3),
            'Supuesto'(p1),
            'Supuesto'(p2),
            'Supuesto'(p3),
            'Supuesto'(p4),
            'Supuesto'(s and !r)
          ]).

:- data counter/1, formula/2, tabular/1, closed/1, opened/1, check/1.
main(Hypotheses, Deduction, Proof) :-
    retractall(counter(_)), retractall(formula(_,_)), retractall(tabular(_)),retractall(closed(_)),retractall(opened(_)),retractall(check(_)),
    assert(counter(0)), assert(tabular(0)),
    format(" T~p  |-  ~p\n\n",[Hypotheses, Deduction]),
    eval(Hypotheses, Deduction, Proof),
    check_pending.

check_pending :-
    setof(Name, check(Name), Pending), !,
    check_pending_(Pending).
check_pending.

check_pending_([]).
check_pending_([Name|Ns]) :-
    retractall(counter(_)),retractall(formula(_,_)), retractall(tabular(_)),retractall(closed(_)),retractall(opened(_)),
    assert(counter(0)), assert(tabular(0)),
    rule(Name, Hypotheses, Deduction, Proof), !,
    numbervars([Hypotheses, Deduction, Proof], 0, _),
    format("\n\n Demostración de la regla derivada ~p:  T~p  |-  ~p\n\n",[Name,Hypotheses,Deduction]),
    eval(Hypotheses, Deduction, Proof), !,
    check_pending_(Ns).

eval(Hypotheses, Deduction, [ Rule | Proof ]) :-
    eval_rule(Rule, Hypotheses),
    eval(Hypotheses, Deduction, Proof).
eval(_, Deduction, []) :-
    check_deduccion(Deduction).

eval_rule(R, P):-
    (   exec(R, P) ->
        output(R)
    ;
        format("\nERROR aplicando\t\t~p", [R]), !, fail
    ).

exec('Premisa'(C), Hypotheses) :- !,
    'Premisa'(C, Hypotheses).
exec(Rule,_) :-
    Rule =.. [Name|Args],
    rule(Name,Hypotheses, Deduction, _Proof), !,
    assert(check(Name)),
    exec_rule(Args, Hypotheses, Deduction).
exec(Rule,_) :-
    catch(call(Rule),_,fail).

'Premisa'(1,[P | _Hypotheses]) :- !,
    add_formula(P).
'Premisa'(A,[_ | Hypotheses]) :-
    A1 is A - 1,
    'Premisa'(A1, Hypotheses).

exec_rule(Args, Hypotheses, Deduction) :-
    see_formulas(Args, Formulas),
    Hypotheses = Formulas,
    add_formula(Deduction).
see_formulas([],[]).
see_formulas([A|As], [FA|FAs]) :-
    formula(A, FA),
    see_formulas(As, FAs).

check_deduccion(Deduction) :-
    retract(counter(C)),
    formula(C, Formula),
    (   \+ opened(_) ->
        (   Formula = Deduction ->
            format("~50|ok",[])
        ;
            format("\nERROR: Fórmula ~w no coincide con lo esperado ~w\n\n",[Formula,Deduction])
        )
    ;
        format("\nERROR: Supuesto no cerrado\n\n",[])
    ).

add_formula(Formula) :-
    next_couonter(C),
    asserta(formula(C, Formula)).

next_couonter(C1) :-
    retract(counter(C)),
    C1 is C + 1,
    asserta(counter(C1)).
    

output(Rule) :-
    tabular(T),
    counter(C),
    formula(C, Formula),
    format("  ~p~5|",[C]),
    format_tabular(T),
    format("~p",[Formula]),
    format("~50|~p\n",[Rule]).    

increase_tab :-
    retract(tabular(Tab)),
    Tab1 is Tab + 1,
    assert(tabular(Tab1)).
decrease_tab :-
    retract(tabular(Tab)),
    Tab1 is Tab - 1,
    assert(tabular(Tab1)).

format_tabular(0) :- !.
format_tabular(T) :-
    T1 is T - 1,
    format("     ",[]),
    format_tabular(T1).


%% Inference Rules
% Conjunction
'I' and (A, B) :-
    formula(A, FA),
    formula(B, FB),
    add_formula(FA and FB).

'E' and a(A) :-
    formula(A, FA and _FB),
    add_formula(FA).
'E' and b(A) :-
    formula(A, _FA and FB),
    add_formula(FB).
% Disjuncion
'E' or (A, B, C) :-
    formula(A, FB or FC),
    formula(B, FB --> F),
    formula(C, FC --> F),
    add_formula(F).

'I' or a(A, Formula) :-
    formula(A, FA),
    add_formula(FA or Formula).
'I' or b(Formula, B) :-
    formula(B, FB),
    add_formula(Formula or FB).
% Negation
'I' ! (A) :-
    formula(A, FA --> B and ! B),
    add_formula(! FA).

'E' ! (A) :-
    formula(A, ! ! FA),
    add_formula(FA).
% Implication
'E' --> (A, B) :-
    formula(A, FB --> FC),
    formula(B, FB),
    add_formula(FC).
'I' --> (A, B) :-
    opened(A),
    formula(A, FA),
    valid(B),
    formula(B, FB),
    close_assumption(A),
    add_formula(FA --> FB).
'Supuesto'(FA) :-
    increase_tab,
    add_formula(FA),
    counter(C),
    assert(opened(C)).
% Bi-Implication
'I' <-> (A, B) :-
    formula(A, FA --> FB),
    formula(B, FB --> FA),
    add_formula(FA <-> FB).
'E' <-> a(A) :-
        formula(A, FA <-> FB),
        add_formula(FA --> FB).
'E' <-> b(A) :-
        formula(A, FA <-> FB),
        add_formula(FB --> FA).


%% Derived Rules
rule( 'MT',
      [ FA --> FB, !FB ],
      !FA,
      [ 'Premisa'(1),
        'Premisa'(2),
        'Supuesto'(FA),
        'E' --> (1, 3),
        'I' and (4, 2),
        'I' --> (3, 5),    
        'I' ! (6)
      ]).
   

% Auxiliary predicates
valid(B) :-
    \+ closed(B).
close_assumption(A) :-
    counter(C),
    between(A, C, C1),
    assert(closed(C1)),
    fail.
close_assumption(A) :-
    decrease_tab,
    retract(opened(A)).

