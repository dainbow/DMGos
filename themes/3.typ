#import "../conf.typ": *

== Частичные порядки. Связь строгих и нестрогих порядков. Максимальные и минимальные, наибольшие и наименьшие элементы, верхние и нижние грани, супремум и инфимум. Изоморфизм порядков. Отношения эквивалентности, фактор-множество. Разбиения и отношения эквивалентности.

#definition[
  Бинарное отношение $R$ называется
  - *Рефлексивным* для множества $Z$, если $forall x in Z : (x, x) in R$
  - *Иррефлексивным*, если $forall x: (x, x) in.not R$
  - *Симметричным*, если $forall x : forall y : x R y => y R x$
  - *Антисимметричным*, если $forall x : forall y : x R y and y R x => x = y$
  - *Транзитивным*, если $forall x : forall y : forall z : x R y and y R z => x R z$
]

#lemma[
  Отношение $R subset.eq A^2$:
  - Рефлексивно $<=> id_A subset.eq R$
  - Иррефлексивно $<=> id_A sect R = emptyset$
  - Симметрично $<=> R subset.eq R^(-1) <=> R = R^(-1) <=> R^(-1) subset.eq R$
  - Антисимметрично $<=> R sect R^(-1) subset.eq id_A$
  - Транзитивно $<=> R compose R subset.eq R$
]

#definition[
  Отношение $R$ на каком-либо множестве называется *строгим частичным порядком* на этом множестве, если $R$ иррефлексивно и транзитивно.
]

#definition[
  Отношение $R$ на каком-либо множестве называется *нестрогим частичным порядком* на этом множестве, если $R$ рефлексивно, транзитивно и антисимметрично.
]

#proposition[
  Пусть $P subset.eq A times B, Q, R$ -- бинарные отношения, тогда
  - $(P^(-1))^(-1) = P$
  - $(P union Q)^(-1) = P^(-1) union Q^(-1)$
  - $overline(P)^(-1) = overline(P^(-1))$
  - $(P union Q) compose R = (P compose R) union (Q compose R)$
  - $(P sect Q) compose R subset.eq (P compose R) sect (Q compose R)$
]

#theorem("Связь строгих и нестрогих порядков")[
  Положим
  #eq[
    $S(A) = {R in cal(P)(A^2) | R "строгий порядок"}$
  ]
  и аналогично выделим множество $N(A)$ всех нестрогих порядков на $A$.

  Рассмотрим функции $phi: S(A) -> cal(P)(A^2)$ и $psi: N(A) -> cal(P) (A^2)$:
  #eq[
    $phi(P) = P union id_A quad psi(Q) = Q without id_A$
  ]

  Тогда утверждается, что
  - $phi(P) in N(A) and psi(phi(P)) = P$
  - $psi(Q) in S(A) and phi(psi(Q)) = Q$
]

#proof[
  Проверим нестрогость $phi(P)$:
  - Рефлексивно, так как $id_A subset.eq phi(P)$
  - Транзитивно, так как
  #eq[
    $phi(P) compose phi(P) = (P union id_A) compose (P union id_A) = \
      (P compose P) union (P compose id_A) union (id_A compose P) union (id_A compose id_A) = \
      (P compose P) union P union id_A subset.eq P union id_A = phi(P)$
  ]
  - Антисимметрично, так как
  #eq[
    $phi(P) sect (phi(P))^(-1) = (P union id_A) sect (P union id_A)^(-1) = \
      (P union id_A) sect (P^(-1) union id_A) =
      (P sect P^(-1)) union id_A = id_A$
  ]
  Итак, $phi(P) in N(A)$. Далее,
  #eq[
    $psi(phi(P)) = (P union id_A) sect overline(id_A) = \
      (P sect overline(id_A)) union emptyset = (P sect overline(id_A)) union (P sect id_A) = P sect (id_A union overline(id_A)) = P sect A^2 = P$
  ]
  Проверим нестрогость $psi(Q)$:
  - Ирефлексивно, так как $id_A sect psi(Q) = emptyset$
  - Транзитивно, так как пусть $x Q y and y Q z$, где $x != y and y != z$. Если $x = z$, то $z Q y and y Q z => z = y$ -- противоречие.
  Итак, $psi(Q) in S(A)$. Далее,
  #eq[
    $phi(psi(Q)) = (Q sect overline(id_A)) union id_A = (Q union id_A) sect (id_A union overline(id_A)) = Q sect A^2 = Q$
  ]
]

#definition[
  Если на множестве $A$ задан строгий частичный порядок $P$, элемент $x in A$ называется *максимальным*, если
  #eq[
    $forall y in A : not (x P y)$
  ]
  В случае нестрогого порядка $Q$ определяется, как
  #eq[
    $forall y in A : x Q y => y = x$
  ]
]

#definition[
  Если на множестве $A$ задан строгий частичный порядок $P$, элемент $x in A$ называется *минимальным*, если
  #eq[
    $forall y in A : not (y P x)$
  ]
  В случае нестрогого порядка $Q$ определяется, как
  #eq[
    $forall y in A : y Q x => y = x$
  ]
]

#definition[
  Если $R$ есть строгий или нестрогий частичный порядок на множестве $A$, пара $(A, R)$ называется *частично упорядоченным множеством (ч.у.м.)*
]

#definition[
  Элемент $x in B$ называется *наибольшим* в подмножестве $B$ ч.у.м. $(A, <)$, если
  #eq[
    $forall y in B : y < x$
  ]
  и *наименьшим*, если
  #eq[
    $forall y in B : x < y$
  ]
]

#definition[
  Пусть $(A, <)$ ч.у.м. и $B subset.eq A$. Элемент $x in A$ назовём *верхней гранью* множества $B$, если
  #eq[
    $forall y in B : y < x$
  ]
  Аналогично определяются *нижние грани*.

  Определим $B^triangle$ -- множество всех верхних граней, а также $B^triangle.b$ -- нижних граней.
]

#definition[
  Мы говорим, что $x in A$ есть *точная верхняя грань (супремум)* множества $B$, если $x$ есть наименьший элемент множества $B^triangle$.

  Аналогично определяется *точная нижняя грань (инфимум)*.
]

#definition[
  Структуры $cal(A) = (A, R); cal(B) = (B, Q)$ *изоморфны*, если существует функция $alpha : A -> B$, т.ч. $A overset(~, alpha) B$ и
  #eq[
    $x R y <=> alpha(x) Q alpha(y)$
  ]
]

#definition[
  Отношение $R subset.eq A^2$ называется *отношением эквивалентности (эквивалентностью)* на $A$, если $R$ рефлексивно, симметрично и транзитивно.
]

#definition[
  Пусть $E$ есть эквивалентность на множестве $A$ и $x in A$. Назовём множество
  #eq[
    $[x]_E = {z in A | x E z}$
  ]
  *классом эквивалентности* элемента $x$ по отношению $E$.
]

#definition[
  Множество
  #eq[
    $A_(\/ E) = {sigma in cal(P)(A) | exists x in A : [x]_E = sigma} = {[x]_E | x in A}$
  ]
  называется *фактор-множеством* множества $A$ по отношению $E$.
]

#definition[
  Назовём множество $Sigma subset.eq cal(P) (A)$ *разбиением* множества $A$, если
  #eq[
    $emptyset in.not Sigma and union Sigma = A and (forall sigma, tau in Sigma : sigma sect tau != emptyset <=> sigma = tau)$
  ]
]
