#import "../conf.typ": *

== Формула бинома Ньютона, полиномиальная формула. Свойства биномиальных коэффициентов: симметричность, унимодальность, рекуррентная формула треугольника Паскаля. Знакопеременная сумма биномиальных коэффициентов. Оценки для биномиальных коэффициентов при $n$: асимптотика $C_n^k$ в случае $j = const dot n$ и в случае $k = o(sqrt(n))$

#theorem("Бином Ньютона")[
  *Биномом Ньютона* называется выражение
  #eq[
    $(a + b)^n = sum_(k = 0)^n C_n^k a^k b^(n - k)$
  ]
]

#proof[
  $n$-ю степень суммы можно записать в виде
  #eq[
    $(a + b)^n = underbrace((a + b) (a + b) ... (a + b), n "раз")$
  ]
  Чтобы получить слагаемое в сумме, мы должны последовательно выбрать из каждой скобки $a$ или $b$, причём любое слагаемое имеет вид $a^k b^(n - k)$.

  Более того, чтобы определить слагаемое, нам необходимо и достаточно знать, сколько $a$ мы выбрали.

  А это для каждого слагаемого можно сделать $C_n^k$ способами.
]

#definition[
  Пусть $n = sum_(i = 1)^t n_i$.

  Для каждого $i in {1, ..., t}$ мы хотим забрать в $a_i$ группу ровно $n_i$ элементов из изначального набора $n$ элементов.

  Количество способов это сделать равно
  #eq[
    $P(n_1, ..., n_t) = C_n^(n_1) C_(n - n_1)^(n_2) ... C_(n - n_1 - ... - n_(t - 1))^(n_t) = \
      n! / (n_1 ! (n - n_1)!) (n - n_1)! / (n_2 ! (n - n_1 - n_2)!) ... (n - n_1 - ... - n_(t - 1))! / (n_t ! (n - n_1 - ... - n_t) !) = \
      n! / (n_1 ! n_2 ! ... n_t !)$
  ]
  Оно называется *полиномиальный коэффициентом*
]

#theorem("Полиномиальная формула")[
  *Полиномиальной формулой* называется выражение
  #eq[
    $(x_1 + ... x_t)^n = sum_(n_1 + ... + n_t = n) P(n_1, ..., n_t) x_1^(n_1)... x_t^(n_t)$
  ]
]

#proof[
  Рассуждения аналогичны доказательству бинома Ньютона
]

#theorem("Свойства биномиальных коэффициентов")[
  - *Симметричность*: $C_n^k = C_n^(n - k)$
  - *Унимодальность*: коэффициенты возрастают до $k = n / 2$, а потом убывают
  - *Треугольник Пакскаля*: $C_n^k = C_(n - 1)^(k - 1) + C_(n - 1)^k$
  - $sum_(k = 0)^n (-1)^k C_n^k = 0$
]

#proof[
  - Выбрать $k$ объектов из $n$ -- это то же самое, что оставить $n - k$ объектов из $n$
  - Отношение $C_n^k / C_n^(k - 1) = (n - k + 1) / k = (n + 1) / k - 1 > 1 <=> (n + 1) / k > 2 <=> k <= n / 2$
  - Заметим, что все наборы можно разбить на две группы:
    - Содержат $n$-й элемент, но помимо него нужно выбрать $k - 1$ элемент из $n - 1$ штук.
    - Не содержат $n$-й элемент, а значит нужно выбрать $k$ из $n - 1$ штук
  - Применим Бином Ньютона для $(1 - 1)^n$
]

#theorem[
  Пусть $a in (0, 1)$.

  Тогда
  #eq[
    $C_n^([a n]) = (1 / (a^a (1 - a)^(1 - a)) + o(1))^n, n -> oo$
  ]
]

#proof[
  Будем пользоваться формулой Стирлинга $n! ~ sqrt(2 pi n) (n / e)^n$:
  #eq[
    $C_n^([a n]) = n! / ([a n]! (n - [a n])!) ~ (sqrt(2 pi n) (n / e)^n) / (sqrt(2 pi [a n]) ([a n] / e)^[a n] sqrt(2 pi (n - [a n])) ((n - [a n]) / e)^(n - [a n])) ~ \
      Theta(1 / sqrt(n)) (n / e)^n / (([a n] / e)^[a n] ((n - [a n]) / e)^(n - [a n])) = Theta(1 / sqrt(n)) n^n / ([a n]^[a n] (n - [a n])^(n - [a n])); quad n -> oo$
  ]
  Теперь предположим, что $a n in NN$, тогда получим
  #eq[
    $C_n^[a n] ~ Theta(1 / sqrt(n)) / (a^(a n) (1 - a)^(n - a n)) = Theta(1 / sqrt(n)) (1 / (a^a (1 - a)^(1 - a)))^n = \
      (1 / (a^a (1 - a)^(1 - a)) + o(1))^n ; quad n -> oo$
  ]
]

#theorem[
  Если $k = o(sqrt(n))$, то $C_n^k ~ n^k / k!$
]

#proof[
  Распишем биномиальный коэффициент:
  #eq[
    $C_n^k = (n (n - 1) ... (n - k + 1)) / k! = n^k / k! (1 - 1 / n) ... (1 - (k - 1) / n) = \
      n^k / k! e^(ln (1 - 1 / n) + ... + ln (1 - (k - 1) / n))$
  ]
  Используем разложение логарифма $ln (1 - x) = -x + O(x^2), x -> 0$:
  #eq[
    $C_n^k = n^k / k! e^(- (k (k - 1)) / n + O(k^3 / n^2)) overset(->, k = o(sqrt(n))\, n -> oo) n^k / k!$
  ]
]