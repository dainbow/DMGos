#import "../conf.typ": *

== Хроматическое число, хроматический индекс, число независимости, кликовое число. Нижняя оценка хроматического числа через число независимости и через кликовое число. Теорема Визинга (с доказательством).

#proposition[
  #eq[
    $chi(G) >= abs(V) / alpha(G)$
  ]
]

#proof[
  Действительно, вершины окрашены в один цвет $<=>$ между никакой парой из них нет ребра $<=>$ они лежат в одном независимом подмножестве.

  #eq[
    $abs(V) = sum_(i = 1)^chi(G) abs(V_i) <= chi(G) max abs(V_i) <= chi(G) alpha(G)$
  ]
]

#definition[
  *Кликовым числом* графа $G$ называется
  #eq[
    $omega(G) = max {k in NN | exists W subset.eq V : abs(W) = k and forall x, y in W : (x, y) in E}$
  ]
]

#proposition("Свойства кликового числа")[
  - $alpha(G) = omega(overline(G))$
  - $chi(G) >= max {omega(G), abs(V) / alpha(G)}$
]

#proof[
  - Очевидно, что наличие ребра между вершинами в графе эквивалентно отсутствию оного в дополнении графа
  - Очевидно, что мы не сможем покрасить граф в число, меньшее велечине максимальной клики, так как вершины в ней попарно связаны
]

#definition[
  *Хроматический индекс* графа $G$ -- минимальное число цветов, в которое можно раскрасить рёбра графа так, что любые два смежных ребра не одноцветны.

  Обозначение $chi' (G)$.
]

#lemma[
  Пусть $G = (V, E)$ и $v$ -- его вершина, причём $deg v <= k$.

  Если степень каждого из соседей $v$ также не превосходит $k$, причём степень $k$ достигается не более чем для одного из соседей $v$, то если рёбра графа $G without {v}$ можно покрасить в $k$ цветов, то в $k$ цветов можно покрасить и рёбра графа $G$
]

#proof[
  Докажем по индукции. Для $k = 1$ -- это либо мост, либо изолированная вершина, доказано.

  Переход. Пусть $u_1, ..., u_m$, где $m = deg v$ -- соседи вершины $v$ в графе $G$, из которых БОО $deg u_1 = k$, а $deg$ остальных равен $k - 1$.

  Тогда в $G' = G without {v}$ они имеют степени $k - 1$ и $k - 2$ соответственно:

  #eq[
    #image("../assets/Vising1.png", width: 40%)
  ]

  Для каждого цвета $i$ пусть $X_i subset.eq {u_1, ..., u_m}$ -- подмножество вершин-соседей, в которые не попадает цвет $i$, то есть, никакие инцидентные им рёбра не раскрашены в этот цвет.

  Тогда вершина $u_1$ имеющая степень $k - 1$ попадает ровно в одно из множеств $X_1, ..., X_k$, а остальные -- ровно в два. Отсюда суммарное число элементов в этих множествах равно
  #eq[
    $sum_(i = 1)^k abs(X_i) = 2 deg v - 1 < 2 k$
  ]
  Пусть число вхождений каких-то двух цветов различается более чем на два, то есть
  #eq[
    $abs(X_i) > abs(X_j) + 2$
  ]
  Тогда рассмотривается подграф $G'_(i, j)$ графа $G'$, образованный рёбрами, раскрашенными в цвета $i$ и $j$.

  Каждый компонент связности в этом подграфе -- это или простой путь, или простой цикл; в них чередуются $i$-рёбра и $j$-рёбра.

  Каждая вершина, не принадлежащая $X_i sect X_j$ попадает в один из этих компонент связности:
  #eq[
    #image("../assets/Vising2.png", width: 30%)
  ]
  Тогда непременно найдётся компонент, в который попадает больше вершин из $X_i$, чем вершин из $X_j$ (по принципу Дирихле). Тогда этот путь можно перекрасить, поменгяв местами цвета $i$ и $j$. При этом $abs(X_i)$ уменьшится на 1 или 2, а $abs(X_j)$ на столько же увеличится.

  Повторив такое перекрашивание необходимое число раз, можно добиться неравенства
  #eq[
    $forall i, j : abs(abs(X_i) - abs(X_j)) <= 2$
  ]
  Поскольку сумма $sum_(i = 1)^k abs(X_i)$ нечётна, то хотя бы одно из её слагаемых должно быть нечётным $=>$ хотя бы одно слагаемое должно быть равно 1, поскольку в противном случае все слагаемые меньше или равны двум, и их сумма будет не менее $2 k$.

  Пусть $X_i = {u_l}$ -- найденное выше множество. Далее, строится граф $tilde(G) = (V, tilde(E))$, полученный из $G$ удалением ребра $(u_l, v)$, а также всех рёбер, покрашенных в $G'$ в цвет $i$.

  Степень вершины $v$ уменьшилась на единицу и степени всех соседей $v$ также уменьшились на единицу каждая -- применимо предположении индукции, согласно которому, рёбра графа $tilde(G)$ раскрашиваются в $k - 1$ цветов.

  Осталось вернуть все удалённые из $G$ рёбра и покрасить их в цвет $i$.
]

#theorem("Визинга")[
  Для любого графа $G$:
  #eq[
    $chi' (G) <= Delta(G) + 1$
  ]
]

#proof[
  Пусть $G_i$ -- подграф $G$ на вершинах $v_1, ..., v_i$.

  Утверждается, что рёбра каждого $G_i$ можно покрасить в $Delta(G) + 1$ цветов.

  База индукции по $i$ очевидна -- одинокая вершина.

  Иначе для перехода применяем лемму, так как степень каждой вершины подграфов $<= Delta(G) + 1$.
]

