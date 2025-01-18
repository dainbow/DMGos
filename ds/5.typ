#import "../conf.typ": *

== Эйлеровы и гамильтоновы циклы в графах: критерий эйлеровости, алгоритм Флёри (с доказательством корректности), достаточное условие гамильтоновости (теорема Дирака или Оре). Признак Эрдеша-Хватала (б/д). Два необходимых условия гамильтоновости.

#definition[
  Граф называется *эйлеровым*, если существует замкнутый маршрут, проходящий по всем рёбрам этого графа ровно один раз.
]

#theorem("Критерий эйлеровости графа")[
  Для связного графа следующие утверждения эквивалентны:
  + Граф эйлеров
  + Степень каждой вершины графа чётна
  + Множество рёбер графа распадается в объединение непересекающихся по рёбрам простых циклов
]

#proof[
  $(1 => 2)$:
  - Эйлеров граф есть цикл, а цикл есть замкнутый маршрут. Вершина, встречающаяся в этом маршруте, как составляющая, задаётся конструкцией $e_i v_i e_(i + 1)$, то есть каждое её вхождение в маршрут увеличивает степень на $2$.

    Вхождение в маршрут первой и последней вершины увеличивают степень только на 1, но так как $v_1 = v_(n + 1)$, то суммарно степень увеличилась на 2
  $(2 => 3)$:
  - Зафиксируем вершину $x_1$ ненулевой степени. Выберем её любую соседнюю вершину $x_2$. Так как $deg (x_2) > 0 and deg (x_2) dots.v 2$, то $exists x_3 != x_1 in V$, связанная ребром с $x_2$.

    Будем идти далее по произвольному ребру из только что выбранной вершины $x_k$, пока не вернёмся в одну из уже выбранных вершин. Тогда мы найдём некоторый простой цикл $Z_1$.

    Удалим все его рёбра из $G$ и получим новый граф, возможно с несколькими компонентами связности. Проделаем аналогичную операцию в каждой из новых компонент связности и замети, что величина $abs(E)$ строго уменьшается.

    Проделав данную операцию индуктивно для каждой компоненты, мы разобьём множество $E$ на требуемое объединение.
  $(3 => 1)$:
  - Доказательство по индукции. Для одного простого цикла утверждение очевидно.

    Предположим, что в $G$ больше простых циклов. Удалим один простой цикл $C$. Полученный граф $G'$ распадается на некоторые компоненты связности, каждая из которых распадается на простые циклы.

    Начнём обходить граф по вершинам цикла $C$, причём если мы попали в вершину $v in V$, лежащую в одной из компонент связности $G'$, то обойдём её по предположению индукции и вернёмся в $v$.

    Продолжим идти по циклу $C$, обходя ещё не посещённые компоненты связности $G'$. Таким образом, мы обойдём весь граф $G$.
]

#proposition("Алгоритм Флёри")[
  - Стартуем из любой вершины графа
  - На каждом шаге проходим ещё не пройденное ребро и удаляем его из графа
  - Идём по мосту только если нет другой возможности
  - Если идти стало некуда, значит эйлеров цикл только что простроен
]

#proof[
  - Построенный алгоритмом маршрут является циклом, так как степень каждой вершины чётная, а значит
    - Невозможна ситуация, когда нам некуда идти,
    - Более того, для достижения чётности начальной вершины, мы обязаны вернуться в неё в конце
  - Мы обойдём все рёбра, так как если бы остались непосещённые рёбра, то на каком-то шаге мы бы прошли по мосту, когда существовала альтернатива (голубые зоны -- потенциально непосещённые рёбра):
    #image("../assets/Floury.png")
]

#definition[
  *Гамильтонов путь* -- простой путь, проходящий через все вершины графа по одному разу
]

#definition[
  *Гамильтонов цикл* -- замкнутый гамильтонов путь
]

#definition[
  Граф называется *гамильтоновым*, если в нём существует гамильтонов цикл
]

#theorem("Дирака")[
  Если в связном графе $n$ вершин и степень любой вершины $>= n / 2$, то этот связный граф -- гамильтонов
]

#proof[
  Пусть $P = v_1 v_2 ... v_k$ -- самый длинный путь в графе $G$.

  Если $v_1$ смежна с некоторой вершиной $x in.not P$, то существует путь длиннее $P$ -- противоречие.

  Аналогичное рассуждение с $v_k => v_k$ и $v_1$ смежны только с вершинами из $P$. Тогда поскольку $deg (v_1) >= n / 2$ и в графе нет петель, то $k >= n / 2 + 1$.

  Далее докажем, что существует $j: v_j$ инцидентна с $v_k$, а $v_(j + 1)$ с $v_1$:
  - Предположим, что такой ситуации не оказалось. Тогда в $P$ есть как минимум $deg (v_1)$ вершин, несвязанных c $v_k$.

    Поскольку все вершины, связанные с $v_k$ находятся в пути и $v_k$ не инцидентна сама с собой, то в $P$ хотя бы $deg(v_1) + deg(v_k) + 1 = n + 1$ вершин -- противоречие.
  Из утверждения выше следует, что в $G$ существует простой цикл $C = v_(j + 1) ... v_k v_j v_(j - 1) ... v_1 v_(j + 1)$. Покажем, что этот цикл -- гамильтонов.

  Предположим, что существует $v in V without C$. Поскольку граф связен, $v$ должна быть связана каким-то путём с некоторой $v_i in C$, но тогда существует путь $P'$ от $v$ до $C ->$ круг по $C$, который длиннее, чем $P$, что противоречит выбору $P$.
]

#definition[
  *Вершинной связностью* графа $G$ называется минимальное количество вершин, в результате удаления которых граф перестанет быть связным.

  Обозначение $kappa (G)$
]

#definition[
  *Числом независимости* графа $G$ называется максимальное количество вершин в свободном от рёбер подмножестве (*независимое подмножество*).

  Обозначение $alpha (G)$
]

#proposition[
  Пусть $G$ -- гамильтонов граф.

  Тогда
  #eq[
    $forall "независимого" W : underbrace(abs(v(W)), "множество соседей") >= abs(W)$
  ]
]

#proof[
  Гамильтонов цикл содержит все вершины, в том числе все $w in W$.

  Заметим, что после любой вершины из независимого множества должна стоять вершина из $v(W)$, так как никакие две вершины в $W$ не связаны.

  А значит соседей у $W$ должно быть как минимум столько же, сколько в нём вершин, чтобы построить корретный цикл.
]

#proposition[
  Пусть $G$ -- гамильтонов граф и $S$ -- произвольное непустое множество вершин.

  Тогда граф $G without S$ имеет не более $abs(S)$ компонент связности.
]

#proof[
  Возьмём гамильтонов цикл исходного графа и, удалив в нём $abs(S)$ точек, в худшем случае он разобьётся на $abs(S)$ компонент связности.
]

#theorem("Эрдеша-Хватала")[
  Пусть количество вершин в графе $G(V, E): abs(V) >= 3$ и $alpha(G) <= kappa(G)$.

  Тогда граф гамильтонов.
]