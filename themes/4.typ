#import "../conf.typ": *

== Принципы математической индукции, «сильной» индукции и наименьшего числа. Их равносильность. Теорема о рекурсии в различных формах (без доказательства). Принцип Дирихле (с доказательством). Основные теоремы о мощностях конечных и счетных множеств (про подмножество, объединение, произведение, степень и пр.; доказательства как доп. вопросы).

#definition[
  *Принцип математической индукции*:
  #eq[
    $forall X subset.eq NN : (0 in X and (forall n in NN: n in X => n + 1 in X)) => X = NN$
  ]
]

#definition[
  Назовём множество $X subset.eq NN$ *прогрессивным*, если
  #eq[
    $forall n in NN : forall m < n : (m in X => n in X)$
  ]
  *Принцип порядковой индукции*:
  #eq[
    $forall X subset.eq NN : X - "прогрессивное" => X = NN$
  ]
]

#definition[
  *Принцип наименьшего числа*:
  #eq[
    $forall X subset.eq NN : X != emptyset => exists min X$
  ]
]

#theorem[
  Следующие утверждения равносильны:
  + Принцип порядковой индукции
  + Принцип наименьшего числа
  + Принцип математической индукции
]

#proof[
  $(1 => 2)$. Предположим, что в некотором $X$ нет наименьшего элемента. Покажем, что $overline(X)$ прогрессивно:
  #eq[
    $forall m < n: m in.not X => n in.not X$
  ]
  ибо иначе $n = min X$, что невозможно.

  По принципу порядковой индукции $overline(X) = NN => X = emptyset$.

  $(2 => 3)$. Рассмотрим множество $overline(X)$. Допустим, что $overline(X) != emptyset$. Тогда $exists n = min overline(X)$.

  По предположению, $n != 0$ (так как $0 in X$). Значит, $n = m + 1$ для некоторого $m in NN$. Поскольку $m < n$, имеем $m in X$, но по предположению должно было быть, что $m + 1 = n in X$, что не так. Следовательно $overline(X) = emptyset, X = NN$.
  $(3 => 1)$. Рассмотрим множество
  #eq[
    $Y = {n in NN | forall m < n : m in X}$
  ]
  Очевидно, $0 in Y$.

  Допустим, что $n in Y$. Тогда $forall m < n: m in X$, что, в силу прогрессивности, влечёт $n in X$, а значит и $n + 1 in Y$.

  Для множества $Y$ мы проверили базу и шаг индукции, а значит $Y = NN$.

  Наконец, для всякого $n in NN$ имеем $n < n + 1 in Y => n in X$. Следовательно, и $X = NN$.
]

#theorem("О рекурсии")[
  Пусть $U$ -- некоторое множество, $u_0 in U$ и $h: U -> U$.

  Тогда существует единственная функция $f: NN -> U$:
  #eq[
    $f(0) = u_0 and forall n in NN : f(n + 1) = h(f(n))$
  ]
]

#theorem("О рекурсии, знающей шаг")[
  Пусть $U$ -- некоторое множество, $u_0 in U$ и $h: NN times U -> U$.

  Тогда существует единственная функция $f: NN -> U$:
  #eq[
    $f(0) = u_0 and forall n in NN : f(n + 1) = h(n, f(n))$
  ]
]

#theorem("О примитивной рекурсии")[
  Пусть $U, V$ -- некоторые множества, $g: V -> U$ и $h: NN times V times U -> U$.

  Тогда существует единственная функция $f: NN times V -> U$:
  #eq[
    $forall v in V : f(0, v) = g(v) and forall n in NN : f(n + 1, v) = h(n, v, f(n))$
  ]
]

#definition[
  Пусть $n in NN$, тогда определим множество
  #eq[
    $underline(n) = {m in NN | m < n} = {0, ..., n - 1}$
  ]
]

#definition[
  Множество $A$ *конечно*, если $exists n in NN : A ~ underline(n)$
]

#definition[
  Множество $A$ *счётно*, если $A ~ NN$
]

#lemma[
  Для каждого $n in NN$, если $f: underline(n + 1) -> underline(n)$, то $f$ не инъекция
]

#proof[
  Предположим противное, пусть найдётся $n in NN$, для которого есть инъекция $f: underline(n + 1) -> underline(n)$.

  Согласно принципу наименьшего числа, расммотрим наименьшее такое $n$.

  Заметим, что инъекция $f: underline(1) -> underline(0) = emptyset$ невозможна. Значит $n != 0 => exists m in NN : n = m + 1$.

  Пусть $f(n) = x in underline(n)$. Рассмотрим функцию $g$, меняющую $m < n$ и $x < n$ местами.

  Ясно, что $g$ -- биекция, а ограничение инъекции $f|_underline(n)$ также является инъекцией. Тогда и $h = g compose f|_underline(n)$ также инъекция.

  Заметим, если $h(k) = m$, то $f|_underline(n) = x$, но $f$ принимала $x$ только на $n$, так что текущая ситуация невозможна из-за инъективности.

  Значит $rng h subset.eq underline(m) => h: underline(m + 1) -> underline(m)$ -- инъекция для $m < n$ -- противоречие.
]

#theorem("Принцип Дирихле")[
  Если $m > n$ и $f: underline(m) -> underline(n)$, то $f$ не инъекция
]

#proof[
  Допустим, $exists m > m: f: underline(m) -> underline(n)$ -- инъекция.

  Но тогда $f|_underline(n + 1) : underline(n + 1) -> underline(n)$ -- тоже инъекция, что противоречит предыдущей лемме.
]

#theorem("Правило подмножеств")[
  Если $A subset.eq NN$, то множество $A$ конечно или счётно.
]

#proof[
  Согласно теореме о рекурсии, существует функция $alpha : NN -> cal(P)(A)$
  #eq[
    $alpha(0) := A and alpha(n + 1) := cases(alpha(n) without {min alpha(n)}\, alpha(n) != emptyset, emptyset\, "else")$
  ]
  Определим $f(m) := min alpha(m)$, тогда будут два случая 
  - $exists n_0 : alpha(n_0) = emptyset$, выберем из таких $n_0$ наименьшее и докажем, что $f: overline(n_0) -> A$ -- биекция
  - Иначе $f: NN -> A$, также является биекцией.
]

#theorem("Правило суммы")[
  Пусть множества $A$ и $B$ конечны и $A sect B = emptyset$.

  Тогда множество $A union B$ тоже конечно, причём
  #eq[
    $abs(A union B) = abs(A) + abs(B)$
  ]
]

#proof[
  Допустим, что $A overset(~, f) underline(n), B overset(~, g) m$. Определим функцию $h: A union B -> underline(n + m)$:
  #eq[
    $h(x) = cases(f(x)\, x in A, n + g(x)\, x in B)$
  ]
  Доказательство её биективности тривиально.
]

#theorem("Правило произведения")[
  Пусть множества $A$ и $B$ конечны.

  Тогда множество $A times B$ тоже конечно, причём
  #eq[
    $abs(A times B) = abs(A) dot abs(B)$
  ]
]

#proof[
  Допустим, что $A overset(~, f) underline(n), B overset(~, g) m$.  Если $m = 0 or n = 0$, то $A times B = emptyset$ -- тривиальный случай.
  
  Определим функцию $h: A times B -> underline(n m)$:
  #eq[
    $h(x, y) = m f(x) + g(y)$
  ]
  Доказательство её биективности тривиально.
]

#theorem("Правило  объединения")[
  Пусть множества $A$ и $B$ конечны.

  Тогда множество $A times B$ тоже конечно, причём
  #eq[
    $abs(A times B) = abs(A) + abs(B) - abs(A sect B)$
  ]
]

#proof[
  Заметим, что $A union B = (A without B) union B$, причём $(A without B) sect B = emptyset$.

  Тогда по правилу суммы
  #eq[
    $abs(A union B) = abs((A without B) union B) = abs(A without B) + abs(B) = abs(A) - abs(A sect B) + abs(B)$
  ]
]

#theorem("Правило степени")[
  Если множество $A$ конечно, то при любом $n in NN$ множество $A^n$ тоже конечно, причём 
  #eq[
    $abs(A^n) = abs(A)^n$
  ]
]

#proof[
  Индукция по $n$ с учётом $A^(n + 1) = A^n times A$.
]
