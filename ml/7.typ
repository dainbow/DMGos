#import "../conf.typ": *

== Структуры и сигнатуры. Изоморфизм структур. Термы и формулы первого порядка. Их значения. Значение формулы при изоморфизме структур. Выразимые отношения и автоморфизмы структуры.

#definition[
  *Структурой* $cal(M)$ называется кортеж $(M, cal(R), cal(F), cal(C))$:
  - $M != emptyset$ -- *носитель структуры*
  - $forall f in cal(F) : exists n in NN : f in M^(M^n)$
  - $forall R in cal(R) : exists n in NN : R subset.eq M^n$
  - $forall c in cal(C) : c in M$
]

#example[
  Пример структуры натуральных чисел
  #eq[
    $(NN, {=, <}, {+, dot}, {0, 1})$
  ]
]

#definition[
  *Сигнатурой* $sigma$ называется кортеж $(rel_sigma, func_sigma, const_sigma)$, причём $rel_sigma != emptyset$ и все элементы кортежа не пересекаются.

  Каждому $R in rel_sigma$ и каждому $f in func_sigma$ поставлено в соответствие натуральное число, оно называется *валентностью* символа. Пишем $R^((n)), f^((n))$.
]

#definition[
  *Интерпретация* сигнатуры $sigma$ -- пара $(cal(M), cal(S))$, где
  - $cal(M)$ -- структура $(M, cal(R), cal(R), cal(F), cal(C))$
  - $cal(S) : rel_sigma union func_sigma union const_sigma -> cal(R) union cal(F) union cal(C)$, причём
    - $forall R^((n)) in rel_sigma : cal(S)(R) in cal(R) and cal(S)(R) subset.eq M^n$
    - $forall f^((n)) in func_sigma : cal(S)(f) in cal(F) and cal(S)(f) in M^(M^n)$
    - $forall c in const_sigma : cal(S)(c) in cal(C)$
]

#definition[
  Пусть $M_1$ и $M_2$ -- две Интерпретации сигнатуры $sigma$.

  Биекция $alpha: M_1 -> M_2$ называется *изомофизмом этих интерпретаций*, если она сохраняет все функции и предикаты структуры.

  Это означает, если $P_1$ и $P_2$ -- два $k$-местных предиката в $M_1$ и $M_2$, соответствующих одному предикатому символу сигнатуры, то
  #eq[
    $forall a_1, ..., a_k in M_1 : P_1(a_1, ..., a_k) = P_2 (alpha(a_1), ..., alpha(a_k))$
  ]
  Аналогично для $k$-местных функций $f_1$ и $f_2$ соответствующих одному функциональному символу, то
  #eq[
    $forall a_1, ..., a_k in M_1 : alpha(f_1(a_1, ..., a_k)) = f_2(alpha(a_1), ..., alpha(a_k))$
  ]
]

#definition[
  Мы считаем, что задано счётное множество *индивидных (предметных)* переменных
  #eq[
    $var = {x_0, x_1, ..., x_n, ...}$
  ]
]

#definition[
  Правила построения множества *термов* $tm_sigma$ над сигнатурой $sigma$:
  - $x in var => x in tm_sigma$
  - $c in const_sigma => c in tm_sigma$
  - $f^((n)) in func_sigma => forall t_1, ..., t_n in tm_sigma : f(t_1, ..., t_n) in tm_sigma$
]

#definition[
  Правила построения множества *формул* $fm_sigma$ над сигнатурой $sigma$ (булевые операции и кванторы рассматриваются как формальные символы):
  - $R^((n)) in rel_sigma => forall t_1, ..., t_n in tm_sigma : R(t_1, ..., t_n) in fm_sigma$
  - $phi, psi in fm_sigma => not phi in fm_sigma, phi and psi in fm_sigma, phi or psi in fm_sigma, phi -> psi in fm_sigma$
  - $x in var, phi in fm_sigma => forall x : phi in fm_sigma, exists x : phi in fm_sigma$
]

#definition[
  *Оценка переменных* -- это любая функция $pi: var -> M$
]

#definition[
  Пусть $t in tm_sigma, pi$ -- оценка.

  Тогда $[t]_cal(M) (pi) in M$ -- *значение $t$ в $cal(M)$ при оценке $pi$*, причём
  - $x in var => [x](pi) = pi(x)$
  - $c in const_sigma => [c](pi) = c^cal(M)$
  - $[f(t_1, ..., t_n)] (pi) = f^cal(M) ([t_1](pi), ..., [t_n] (pi))$
]

#definition[
  Пусть $phi in fm_sigma, pi$ -- оценка.

  Тогда $[phi]_cal(M) (pi) in {0, 1}$ -- *значение формулы $phi$ в $cal(M)$ при оценке $pi$*, причём
  - $[R(t_1, ..., t_n)] (pi) = 1 <=> ([t_1](pi), ..., [t_n](pi)) in R^cal(M)$
  - $[phi -> psi](pi) = 1 <=> [phi](pi) -> [psi](pi)$
  - $[forall x : phi](pi) = 1 <=> forall a in M : [phi] (pi_x^a) = 1$, где
  #eq[
    $pi_x^a (y) = cases(a\, y = x, pi(y)\, "else")$
  ]
  - $[exists x : phi](pi) = 1 <=> exists a in M : [phi] (pi_x^a) = 1$
]

#definition[
  Определим функцию, возвращающую *переменные формулы или терма*.

  Пусть $V: tm_sigma union fm_sigma -> cal(P) (var)$, причём
  - $x in var => V(x) = {x}$
  - $c in const_sigma => V(c) = emptyset$
  - $V(f(t_1, ..., t_n)) = union_(i = 1)^n V(t_i)$
  - $V(R(t_1, ..., t_n)) = union_(i = 1)^n V(t_i)$
  - $V(phi and psi) = V(phi) union V(psi)$
  - $V(forall x: phi) = V(phi) union {x}$
]

#definition[
  Определим функцию, возвращающую *свободные переменные формулы*

  Пусть $F V: fm_sigma -> cal(P)(var)$, причём:
  - $F V(R(t_1, ..., t_n)) = V(R(t_1, ..., t_n))$
  - $F V(phi or psi) = F V(phi) union F V(psi)$
  - $F V(forall x : phi) = F V(phi) without {x}$
]

#theorem[
  Значение терма $t in tm_sigma$ зависит лишь от значения оценки на $V(t)$.

  Значение формулы $phi in fm_sigma$ зависит лишь от значения оценки на $F V(phi)$.
]

#definition[
  Пусть
  - $fm_sigma (x_1, ..., x_n) := {phi in fm_sigma | F V(phi) subset.eq {x_1, ..., x_n}}$
  - $tm_sigma (x_1, ..., x_n) := {t in tm_sigma | V(t) subset.eq {x_1, ..., x_n}}$
]

#corollary[
  Переопределим значения термов и формул, независимо от оценки.

  Пусть $t in tm_sigma (x_1, ..., x_n), phi in fm_sigma (x_1, ..., x_n)$:
  - $[t]_cal(M) (arrow(a)) := [t]_cal(M) (pi_(x_1 ... x_n)^(a_1 ... a_n))$
  - $[phi]_cal(M) (arrow(a)) := [phi]_cal(M) (pi_(x_1 ... x_n)^(a_1 ... a_n))$
]

#theorem("Значение формулы при изоморфизме")[
  Пусть $cal(M), cal(N)$ -- $sigma$-структуры и $cal(M) overset(tilde.eq, alpha) cal(N)$. Пусть $t in tm_sigma (arrow(x)), phi in fm_sigma (arrow(x))$.

  Тогда
  - $forall arrow(a): [t]_cal(M) (arrow(a)) = [t]_cal(N) (alpha arrow(a))$
  - $forall arrow(a): [phi]_cal(M) (arrow(a)) = [phi]_cal(N) (alpha arrow(a))$
]

#proof[
  Доказывается очевидной индукцией по построению термов и функций.
]

#definition[
  *Отношение* $X subset.eq M^n$ *выразимо в $sigma$-структуре* $cal(M) <=> exists X in fm_sigma (x_1, ..., x_n) : phi^cal(M) = X$
]

#definition[
  *Функция* $f : M^n -> M$ *выразима в $sigma$-структуре* $cal(M) <=> exists t in tm_sigma (x_1, ..., x_n) : t^cal(M) = f$
]

#definition[
  *Автоморфизмами* структуры $cal(M)$ называют множество
  #eq[
    $"Aut" (cal(M)) = {alpha | cal(M) overset(tilde.eq, alpha) cal(M)}$
  ]
]
