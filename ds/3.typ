#import "../conf.typ": *

== Определение простого графа, орграфа, мультиграфа, псевдографа, гиперграфа. Маршруты в графах, пути и простые пути, степени вершин. Изоморфизм графов, гомеоморфизм графов. Понятия связности и компонент связности. Три эквивалентных определения деревьев (с использованием условий ацикличности, связности, числа вершин и ребер) с доказательством их эквивалентности. Блоки и точки сочленения, теорема о пересечении блоков (с доказательством) и теорема о графе блоков и точек сочленения (б/д).

#definition[
  *Графом* называется пара множеств $(V, E) = G$, где $V$ -- множество каких-то объектов, а $E$ -- множество пар объектов из $V$.
]

#definition[
  *Ориентированным графом* $G$ называется пара $G = (V, E)$, где $V$ -- множество вершин, а $E subset.eq V times V$ -- множество *дуг*.
]

#definition[
  *Граф с петлями (псевдограф)* -- граф, в котором есть ребро, исходящее из вершины и возвращающееся в ту же вершину
]

#definition[
  Если $v_1, v_2$ -- вершины, а $e = (v_1, v_2)$ -- соединяющее их ребро, тогда вершина $v_1$ и ребро $e$ *инцидентны*, вершина $v_2$ и ребро $e$ тоже инцидентны.
]

#definition[
  *Граф с кратными рёбрами (мультиграф)* -- граф, имеющий рёбра, инцидентные одной паре вершин.
]

#definition[
  *Маршрутом* в графе $G = (V, E)$ называется последовательность $v_1 e_1 v_2 ... e_n v_(n + 1)$, где вершины $v_i$ могут повторяться, а рёбра $e_j$ инцидентно вершинами $v_j, v_(j + 1)$
]

#definition[
  Если все рёбра в маршруте различны, то замкнутый ($v_1 = v_(n + 1)$) маршрут называется *циклом*, а незамкнутый -- *путём (цепью)*.
]

#definition[
  Пусть или цикл называется *простым*, если все вершины в нём различны
]

#definition[
  Две вершины $u$ и $v$ называются *связанными*, если в графе $G$ существует путь из $u$ в $v$.
]

#definition[
  *Компонентой связности* называется класс эквивалентности относительно связности.
]

#definition[
  Граф называется *связным*, если он состоит из одной компоненты связности.

  В противном случае граф называется *несвязным*.
]

#definition[
  *Гиперграфом* называется пара $H = (V, E)$, где $V$ -- множество вершин, а $E$ -- произвольное подмножество $cal(P)(V)$.
]

#definition[
  Гиперграф называется *$k$-однородным* ($k >= 2$), если $forall a in E : abs(a) = k$
]

#definition[
  Операция *подразделения* ребра показана на рисунке:
  #image("../assets/razdel.png")
]

#definition[
  Два графа называются *гомеоморфными*, если от одного можно перейти к другому при помощи подразделения ребра и обратных к ним
]

#definition[
  Два графа $G_1, G_2$ называются *изоморфными*, если существует такая перестановка $phi: V(G_1) -> V(G_2)$:
  #eq[
    $forall (u, v) in E(G_1) : (phi(u), phi(v)) in E(G_2)$
  ]
]

#definition[
  Связный граф без циклов называется *деревом*.
]

#theorem[
  Для графа $G = (V, E)$ эквивалентны следующие утверждения:
  + $G$ -- дерево
  + Любые две вершины графа $G$ соединены единственным простым путём
  + $G$ -- связен и $abs(V) = abs(E) + 1$
  + $G$ -- ацикличен и $abs(V) = abs(E) + 1$
]

#proof[
  $(1 => 2)$:
  - Граф связен, поэтому любые две вершины соединены путём
  - Граф ацикличен, значит путь единственнен, а также прост, поскольку никому путь не может зайти в одну вершину два раза, потому что это противоречит ацикличности
  $(2 => 3)$:
  - Очевидно, что граф связан, так как любые две вершины соединены простым путём
  - Докажем по индукции соотношение $abs(V) = abs(E) + 1$:
    - Утверждение очевидно для связных графов с одной и двумя вершинами
    - Предположим, что оно верно для графов имеющих меньше $p$ вершин
    - Если же граф $G$ имеет $p$ вершин, то удаление из него любого ребра делает граф $G$ несвязным в сиду единственности простых цепей, более того, получаемый граф будет иметь в точности две компоненты. По предположению индукции, в каждой компоненте число вершин на единицу больше числа рёбер.
  $(3 => 4)$:
  - Представим, что мы добавляем рёбра в граф, после каждого добавления мы обязаны увеличивать наибольшую компоненту связности на 1, иначе в конце граф не станет связным
  - Если между какими-то двумя вершинами образовался цикл, то на какой-то итерации мы бы не увеличили компоненту связности, что противоречит условию
  $(4 => 1)$:
  - Обратно, если мы добавляем по ребру, то в следствие ацикличности, мы должны увеличивать максимальную компоненту связности на 1, иначе после какого-то шага в одной из компонент образуется цикл, что противоречит ацикличности
  - Значит после добавления всех рёбер останется 1 компонента связности, что эквивалентно связности графа
]

#definition[
  *Мост* -- это ребро, после удаления которого увеличивается число компонент связности
]

#definition[
  *Точка сочленения* -- это вершина, после удаления которой увеличивается число компонент связности
]

#definition[
  *Блок* -- это максимальный по включению связный подграф в графе, в котором нет собственных точек сочленения
]

#theorem[
  Любые 2 блока в графе либо не пересекаются, либо пересекаются ровно по одной точке, причём она является точкой сочленения всего графа
]

#proof[
  Пусть 2 блока пересекаются по $>= 2$ точкам. Тогда рассмотрим подграф-объединение этих двух блоков
  - Если мы удалим точку в любом из изначальных блоков, то количество компонент связности не изменится по определению
  - Если мы удалим какую-либо из точек пересечения, то останется хотя бы 1 другая, что также не изменит количество компонент связности объединения подграфов
  - Получили противоречие с минимальностью по включению каждого из блоков
]

#theorem[
  Пусть $G$ -- связный граф, а $C = {c_1, ..., c_k}$ -- его точки сочленения и $B = {b_1, ..., b_l}$ -- его блоки.

  Тогда граф $G' = (V', E')$, где
  - $V' = C union B$
  - $E' = {(b, c) in B times C | c in b} union {(c, b) in C times B | c in b}$
  Является деревом
]
