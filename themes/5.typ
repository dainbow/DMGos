#import "../conf.typ": *

== Вполне упорядоченные множества (ВУМ). Теорема о строении элементов ВУМ. Начальные отрезки ВУМ и их свойства; теорема о сравнении ВУМ (доказательство как доп. вопрос). Сложение и умножение ВУМ; свойства этих операций.

#definition[
  Порядок $<$ на множестве $A$ называется *линейным*, если любые два элемента $A$ сравнимы.

  Мы говорим, что ч.у.м. $(A, <)$ есть *линейно упорядоченное множество (л.у.м.)*, если порядок $<$ линейный.
]

#definition[
  Порядок $<$ на множестве $X$ *фундирован*, если во всяком непустом $Y subset.eq X$ существует минимальный элемент.

  Множество *вполне упорядоченно (в.у.м.)*, если оно линейно и фундировано.
]

#definition[
  Для элемента $x$ в.у.м. $(X, <)$ введём обозначение
  #eq[
    $[0, x) := {y | y < x}$
  ]
  Элемент $x$ называется *предельным*, если
  #eq[
    $x in lim <=> x = sup[0, x) and x != 0$
  ]
  Наименьший элемент в.у.м. $0$ тоже иногда считают предельным, поскольку $0 = sup emptyset = sup [0, 0)$, мы не станем этого делать, но обозначим
  #eq[
    $lim^* = lim union {0}$
  ]
]

#proposition("Свойства предельных элементов")[
  Следующие условия эквивалентны:
  - $x in lim^*$
  - $forall y : not (y + 1 = x)$
  - $forall y < x : y + 1 < x$
]

#theorem("О строении элементов в.у.м.")[
  Всякий элемент $x in X$ однозначно однозначно представим в виде $x = y + n$, где $y in lim^*$
]

#proof[
  Если $x = 0$, то всё доказано.

  Пусть $x > 0$. Рассмотрим множество
  #eq[
    $C = {z in X | exists k in NN_+ : z + k = x}$
  ]
  Если $C = emptyset$, то $forall z in X : z + 1 != x => x$ -- предельный. (по свойствам выше)

  Иначе $C != emptyset => exists z' := min C$ и для некоторого $k' > 0 : x = z' + k'$.

  Если $z' = 0$, то $y = 0, n = k'$. Если же $z' in.not lim$, то по свойствам $exists z'' : z' = z'' + 1$, что противоречит минимальности $z' => z' in lim$. Значит можно брать $y = z', n = k'$.

  Пусть $x = y_1 + n_1 = y_2 + n_2$. Если БОО $n_1 < n_2$, то $y_1 = y_2 + (n_2 - n_1)$, что противоречит предельности $y_1 => n_1 = n_2 => y_1 = y_2$, всё доказали.
]

#definition[
  Подмножество $I$ в.у.м. $X$ называется *начальным отрезком*, если оно "замкнуто вниз":
  #eq[
    $forall x in I : forall y < x : y in I$
  ]
  Если $I != X$, то это *собственный начальный отрезок*.
]

#proposition("Свойства начальных отрезков в.у.м.")[
  Пусть $(X, <)$ в.у.м. Тогда
  + $X$ есть свой начальный отрезок
  + Пусть $I_a$ -- н.о. $X$ при всех $a in A$. Тогда $union_(a in A) I_a$ тоже н.о.
  + Если $x in X$, то $[0, x)$ есть н.о. $X$
  + Если $I$ собственный н.о. $X$, то существует и единственен такой $x in X: I = [0, x)$
  + Пусьб $cal(I) = {I | I - "начальный отрезок" X}$. Тогда $(cal(I), subset.eq)$ есть в.у.м.
  + $(cal(I), subset.eq) tilde.eq X + 1; (cal(I) without X, subset.eq) tilde.eq X$
]

#proof[
  2. Пусть $x in union_(a in A) and y < x$. Тогда найдётся $I_a in.rev x => y in I_a subset.eq union_(a in A) I_a$

  4. Имеем $X without I != emptyset$. Возьмём наименьший $x$ элемент этого множества. Очевидно $y < x => y in I$. Причём если $x <= y => x in I$ -- не может быть.

  5. Порядок $(cal(I), subset.eq)$ линеен: все собственные н.о. вложены в $X$ и сравнимы между собой по предыдущему пункту. Выделим в произвольном подмножестве $cal(J) subset.eq cal(I)$ наименьший элемент. Если $cal(J) = {X}$, то всё ясно. Иначе возьмём в непустом множестве ${x | [0, x) in cal(J) without X}$ наименьший элемент $x'$.

  6. Изоморфизм строится как $[0, x) |-> x$, а $X$ переходит в наибольший элемент множества $X + 1$.
]

#definition("Сравнение в.у.м.")[
  #eq[
    $A < B <=> A "изоморфен собственному н.о." B$
  ]
]

#lemma[
  Пусть $(X, <)$ -- в.у.м. и функция $f: X -> X$ монотонна. Тогда
  #eq[
    $forall x in X : f(x) >= x$
  ]
]

#proof[
  От противного. Тогда подмножество
  #eq[
    $C := {x | f(x) < x} != emptyset$
  ]
  Пусть $x'$ его наименьший элемент. Имеем $f(x') < x'$ по монотонности, но тогда $f(f(x')) < f(x') => f(x') in C$, т.е. $x'$ не наименьший.
]

#theorem("О сравнении в.у.м.")[
  Пусть $C$ -- в.у.м. и $B subset.eq C$. Тогда $B <= C$.
]

#proof[
  Допустим $B > C$. Тогда, по определению
  #eq[
    $exists b in B : C overset(tilde.eq, f) [0_B, b) subset B$
  ]
  Поскольку $b in C$, то $f(b) < b$, но $f$ монотонна, как изоморфизм, а значит $f(b) >= b$ (по предыдущей лемме) -- противоречие.
]

#definition[
  *Произведением* $A B$ в.у.м. $(A, <_A)$ и $(B, <_B)$ называется $(A times B, <)$:
  #eq[
    $(a_1, b_1) < (a_2, b_2) := (b_1 <_B b_2) or ((b_1 = b_2) and (a_1 <_A a_2))$
  ]
]

#definition[
  *Сумма* в.у.м. $A + B$ есть $(A times {0} union B times {1}, <)$:
  #eq[
    $(x, epsilon) < (y, delta) := (epsilon < delta) or ((epsilon = delta = 0) and (x <_A y)) or ((epsilon = delta = 1) and (x <_B y))$
  ]
]

#lemma("Свойства операций над в.у.м.")[
  + $A + (B + C) tilde.eq (A + B) + C$
  + $A(B C) tilde.eq (A B) C$
  + $C(A + B) tilde.eq C A + C B$
]