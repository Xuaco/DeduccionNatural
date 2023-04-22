%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                          Copyright (C)2023 Joaquín Arias (URJC)
%  Name: deduccion.pl
%  Author: Joaquín Arias
%  Date: 4 March 2023
%  Purpose: Execute Natural Deduction Proofs
%  LICENSE: Apache License 2.0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(_,_).

:- op(200, fy, !).
:- op(400, xfy,[and, or, not, !]).
:- op(600, xfy,[-->, <->]).

%% Ejemplos
ejemplo1 :-
    main([s and p or q, p --> ! r, q --> ! r], s and ! r, ['Premisa'(1), 'E' and b(1), 'Premisa'(2), 'Premisa'(3), 'E' or (2,3,4), 'E' and a(1), 'I' and (6,5)]).

ejemplo2 :-
    main([!p --> q and !q],p,['Premisa'(1),'I' ! (1), 'E' ! (2)]).

ejemplo3 :-
    main([p --> !r,!r-->q,p],q,['Premisa'(1),'Premisa'(3), 'E' --> (1,2),'Premisa'(2), 'E' --> (4,3)]).

ejemplo4 :-
    main([p --> q,q-->r],p-->r, ['Premisa'(1),'Premisa'(2),'Supuesto'(p),'E' --> (1,3),'E' --> (2,4),'I' --> (3,5)]).

ejemploMT :-
    main([r --> (q and s), !(q and s)], !r, ['Premisa'(1), 'Premisa'(2), 'MT'(1,2)]).

ejemploSupuesto :- %% Falla porque no esta cerrado el supuesto :-)
    main([s and p or q, p --> ! r, q --> ! r], s and ! r, ['Premisa'(1), 'E' and b(1), 'Premisa'(2), 'Premisa'(3), 'Supuesto'(p1),'Supuesto'(p2),'Supuesto'(p3),'Supuesto'(p4),'Supuesto'(s and !r)]).

%%%% EJEMPLOS SHELL %%%%
shell_ok(Shell) :-
    main_shell([s and p or q, p --> ! r, q --> ! r], s and ! r, ['Premisa'(1), 'E' and b(1), 'Premisa'(2), 'Premisa'(3), 'E' or (2,3,4), 'E' and a(1), 'I' and (6,5)],Shell).
shell_error(Shell) :-
    main_shell([s and p or q, p --> ! r, q --> ! r], s and ! r, ['Premisa'(1), 'E' and b(1), 'Premisa'(2), 'Premisa'(3), 'E' or (2,5,4), 'E' and a(1), 'I' and (6,5)],Shell).


:- data counter/1, formula/2, tabular/1, cerrado/1, hay_supuesto/1, probar/1.
main(Premisas, Deduccion, ReglasInferencia) :-
    retractall(counter(_)), retractall(formula(_,_)), retractall(tabular(_)),retractall(cerrado(_)),retractall(hay_supuesto(_)),retractall(probar(_)),
    assert(counter(0)), assert(tabular(0)),
    format(" T~p  |-  ~p\n\n",[Premisas, Deduccion]), add_proof_line(["START", [Premisas,Deduccion]]),
    eval(Premisas, Deduccion, ReglasInferencia),
    probar_pendientes.

:- data proof/1.
main_shell(Premisas, Deduccion, ReglasInferencia, Proof) :-
    init_proof,
    if(main(Premisas, Deduccion, ReglasInferencia),true,true),       
    proof(Proof).

init_proof :-
    retractall(proof(_)),
    assert(proof([])).

add_proof_line(Line) :-
    retract(proof(L0)),
    make_string(Line,SLine),
    append(L0,[SLine],L1),
    assert(proof(L1)).


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
    format("\n\n Prueba de la regla derivada ~p:  T~p  |-  ~p\n\n",[Nombre,Premisas,Deduccion]), add_proof_line(["START Regla",[Nombre,Premisas,Deduccion]]),
    eval(Premisas, Deduccion, Prueba), !,
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
        format("\nERROR aplicando\t\t~p",[R]), add_proof_line(["ERROR regla",[R]]), !, fail
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
            format("~50|ok",[]), add_proof_line(["OK",[]])
        ;
            format("\nERROR: Resultado ~w no coincide con lo esperado ~w\n\n",[Resultado,Deduccion]), add_proof_line(["ERROR resultado",[Resultado,Deduccion]])
        )
    ;
        format("\nERROR: Supuesto no cerrado\n\n",[]), add_proof_line(["ERROR supuesto",[]])
    ).

add_formula(Formula) :-
    next_couonter(C),
    asserta(formula(C,Formula)).

next_couonter(C1) :-
    retract(counter(C)),
    C1 is C + 1,
    asserta(counter(C1)).
    

output(Regla) :-
    tabular(T),
    counter(C),
    formula(C,Formula),
    format("  ~p~5|",[C]),
    format_tabular(T),
    format("~p",[Formula]),
    format("~50|~p\n",[Regla]),
    add_proof_line(["REGLA",[C,T,Formula,Regla]]).    

format_tabular(0) :- !.
format_tabular(T) :-
    T1 is T - 1,
    format("     ",[]),
    format_tabular(T1).


%% Reglas de inferencia
% Conjunción
'I' and (A,B) :-
    formula(A,FA),
    formula(B,FB),
    add_formula(FA and FB).

'E' and a(A) :-
    formula(A,FA and _FB),
    add_formula(FA).
'E' and b(A) :-
    formula(A,_FA and FB),
    add_formula(FB).
% Disyunción
'E' or (A,B,C) :-
    formula(A,FB or FC),
    formula(B,FB --> F),
    formula(C,FC --> F),
    add_formula(F).

'I' or a(A,Formula) :-
    formula(A,FA),
    add_formula(FA or Formula).
'I' or b(Formula,B) :-
    formula(B,FB),
    add_formula(Formula or FB).
% Negación
'I' ! (A) :-
    formula(A, FA --> B and ! B),
    add_formula(! FA).

'E' ! (A) :-
    formula(A, ! ! FA),
    add_formula(FA).
% Implicación
'E' --> (A,B) :-
    formula(A, FB --> FC),
    formula(B, FB),
    add_formula(FC).
'I' --> (A,B) :-
    hay_supuesto(A),
    formula(A,FA),
    valid(B),
    formula(B,FB),
    cierra(A),
    add_formula(FA --> FB).
'Supuesto'(FA) :-
    increase_tab,
    add_formula(FA),
    counter(C),
    assert(hay_supuesto(C)).
% Doble implicación
'I' <-> (A,B) :-
    formula(A,FA --> FB),
    formula(B,FB --> FA),
    add_formula(FA <-> FB).
'E' <-> a(A) :-
        formula(A,FA <-> FB),
        add_formula(FA --> FB).
'E' <-> b(A) :-
        formula(A,FA <-> FB),
        add_formula(FB --> FA).


%% Predicados derivados
exec_regla(Args,Premisas,Deduccion) :-
    see_formulas(Args,Formulas),
    Premisas = Formulas,
    add_formula(Deduccion).
see_formulas([],[]).
see_formulas([A|As],[FA|FAs]) :-
    formula(A,FA),
    see_formulas(As,FAs).

regla('MT',[FA --> FB,!FB],!FA,
      ['Premisa'(1),
       'Premisa'(2),
       'Supuesto'(FA),
       'E' --> (1,3),
       'I' and (4,2),
       'I' --> (3,5),    
       'I' ! (6)
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


%%% Aux %%%

:- use_module(engine(basic_props)).
make_string([],[]).
make_string([T|Ts],[T|STs]) :-
    number(T), !,
    make_string(Ts,STs).
make_string([T|Ts],[T|STs]) :-
    string(T), !,
    make_string(Ts,STs).
make_string([T|Ts],[ST|STs]) :-
    list(T),
    !,
    make_string(T,ST),
    make_string(Ts,STs).
%% make_string([T|Ts],[ST|STs]) :-
%%     struct(T),
%%     !,
%%     T =.. Struct,
%%     make_string(Struct,ST),
%%     make_string(Ts,STs).
make_string([T|Ts],[ST|STs]) :-
    format_to_string("~p",[T],ST),
    make_string(Ts,STs).



print_shell([]).
print_shell([[]]) :- !,
    print('[]').
print_shell([S]) :-
    string(S), !,
    format("~s",[S]).
print_shell([S|Ss]) :-
    string(S), !,
    format("~s",[S]),
    print(' , '),
    print_shell(Ss).
print_shell([S]) :-
    list(S), !,
    display(' [ '),
    print_shell(S),
    display(' ] ').
print_shell([S|Ss]) :-
    list(S), !,
    display(' [ '),
    print_shell(S),
    display(' ] , '),
    print_shell(Ss).
print_shell([S]) :- !,
    format("~p",[S]).
print_shell([S|Ss]) :-
    format("~p",[S]),
    print(' , '),
    print_shell(Ss).

