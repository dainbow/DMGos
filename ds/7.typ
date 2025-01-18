#import "../conf.typ": *

== Системы общих представителей (с.о.п.): определение, примеры задач, сводящихся к построению с.о.п.. Тривиальные верхняя и нижняя оценки размера минимальной с.о.п.. Жадный алгоритм построения с.о.п., теорема о верхней оценке размера «жадной с.о.п.». Теорема о неулучшаемости этой оценки в общем случае (б/д).

#definition[
  Определим гиперграф $H = (R_n, cal(M))$, где
  - $R_n := {1, ..., n}$
  - $cal(M) subset.eq cal(P)(R_n)$

  Тогда *системой общих представителей (соп)* для совокупности множеств $cal(M)$ назовём любое
  #eq[
    $S subset.eq R_n : forall M in cal(M) : M sect S != emptyset$
  ]
  Также введём величину $tau(cal(M))$ -- минимальная мощности соп для данной совокупности множеств $cal(M)$

  Пусть $forall M in cal(M) : abs(M_i) = k; abs(cal(M)) = s$ и $M_i subset.eq R_n$.

  При фиксированных $n, s, k$ обозначим $cal(M)$ с такими параметрами за $cal(M)(n, k, s)$.
]

#theorem("Тривиальная оценка сверху")[
  #eq[
    $forall n, k, s in NN: forall cal(M)(n, k, s) : tau(cal(M)) <= min {s, n - 1}$
  ]
]

#proof[
  От $n - k + 2$ до $n$ ровно $k - 1$, а значит если мы возьмём все числа от 1 до $n - k + 1$, то мы не сможем получить пустое пересечение с каким-либо представителем, так как в нём не найдётся $k$ не взятых нами чисел.
]

#theorem("Тривиальная оценка снизу")[
  #eq[
    $forall n, k, s in NN: exists cal(M)(n, k, s) : tau(cal(M)) >= min {[n / k], s}$
  ]
]

#proof[
  Возможны два случая:
  + $s <= [n / k]$. Тогда $cal(M) = {{1, ..., k}, {k + 1, ..., 2 k}, ..., {(s - 1)k + 1, ..., s k}}$
  + $s > [n / k]$. В таком случае строим систему $cal(M)$ аналогично предыдущему случаю, но в дополнение добиваем её до $s$ случайным подмножествами.
]

#theorem("Жадный алгоритм")[
  По сути, формулировка есть в шпаргалке.

  #eq[
    $forall n, k, s : forall cal(M) (n, k, s) : tau(cal(M)) <= max{n / k, n / k ln (s k) / n} + n / k + 1$
  ]
]

#proof[
  Возможны следующие случаи:
  + $s <= n / k => tau(cal(M)) <= s <= n / k$
  + $n / k ln (s k) / n >= n => tau(cal(M)) <= n <= n / k ln (s k) / n$
  + $s > n / k and n / k ln (s k) / n < n$
  Для доказательства последнего случая воспользуемся жадным алгоритмом построения соп.

  Возьмём любой элемент $nu_1 in R_n$, который принадлежит наибольшему числу множеств в $cal(M)$.

  Пусть их $rho_1$ штук. Тогда $rho_1 >= (s k) / n$, поскольку $s k = sum_(i = 1)^n sum_(M in cal(M)) II {i in M} <= rho_1 n$.

  Выкинем из $cal(M)$ все множества, содержащие $nu_1$. Осталась совокупность $cal(M)_1: abs(cal(M)_1) = s - rho_1 =: s_1$. Снова сделаем шаг жадного алгоритма.

  Сделаем $N = [n / k ln (s k) / n] + 1$ шагов жадного алгоритма, причём $rho_i >= (s_(i - 1) k) / n$.

  После этого имеем построенное жадным алгоритмом множество $S = {nu_1, ..., nu_N}$ и совокупность $cal(M)_N$, такую, что
  #eq[
    $abs(cal(M)_n) = s_N = s_(N - 1) - rho_N <= s_(N - 1) - (s_(N - 1) k) / n <= ... <= \
      s(1 - k / n)^N = s e^(N ln (1 - k / n)) <= s e^( - (k N) / n) <= s e^(- ln (k s) / n) = n / k$
  ]
  Итого $tau(cal(M)) <= M + n / k <= n / k ln (s k) / n + 1 + n / k$
]

#theorem("Неулучшаемость жадной соп")[
  По сути, формулировка есть в шпаргалке.

  Пусть $k, s$ такие, что
  #eq[
    $exists n_0 : forall n >= n_0 : 2 <= ln (s k) / n <= k <= n / 8: exists cal(M) (n, k, s) : tau(cal(M)) >= 1 / 16 n / k ln (s k) / n$
  ]
]
