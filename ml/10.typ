#import "../conf.typ": *

== Вычислимые функции (на основе интуитивного понятия об алгоритме). Разрешимые и перечислимые множества; их свойства. Универсальные вычислимые функции и T-предикаты. Неразрешимость проблем самоприменимости и остановки. Теорема Клини о неподвижной точке (без доказательства). Теорема о рекурсии. Теорема Райса–Успенского

#definition[
  Частичная функция $f: A overset(->, p) B$ *вычислима*, если существует алгоритм, который на любом входе $x in dom f$ выписывает $f(x)$ и завершается, а на любом входе $x in A without dom f$ не завершается ни за какое конечное количество шагов.
]

#definition[
  Множество $A$ *разрешимо*, если его характеристическая функция $chi_A$ вычислима.
]

#definition[
  Множество $A$ *перечеслимо*, если есть алгоритм, на пустом входе последовательно выписывающий все элементы $A$ и только их.
]

#proposition[
  Каждое конечное множество разрешимо
]

#proof[
  Переберём все его элементы за конечное время и определим, принадлежит ли вход ему
]

#proposition[
  Каждое разрешимое множество перечеслимо
]

#proof[
  Поочерёдно будем считать результат характеристической функции на всех числах из $NN$ и печатать, если функция вернула $1$.
]

#proposition[
  Если $A, B$ разрешимы, то разрешимы
  - $A union B$
  - $A sect B$
  - $A times B$
  - $overline(A)$
]

#proof[
  Выразим характеристические функции полученных множеств через характеристические функции $A$ и $B$
]

#proposition[
  Если $A, B$ перечеслимы, то перечеслимы
  - $A union B$
  - $A sect B$
  - $A times B$
  - $"pr"^i A$
]

#proof[
  Будем запускать перечесляющие алгоритмы "параллельно" -- чередовать их по одному шагу и потоки вывода:
  - Сливать в один
  - Если число, выведенное одним из потоком выводилось другим, то выводим его
  - При получении нового числа из первого потока, декартово умножаем его на все числа из второго потока и выводим пары
]

#definition[
  Частичная функция $U: NN^2 overset(->, p) NN$ называется *универсальной вычислимой*, если она вычислима и для всякой вычислимой функции $f: NN overset(->, p) NN$ найдётся число $n in NN$, называемое *индексом* функции $f$ относительно $U$, такое что $U_n = f$.
]

#definition[
  Для каждой у.в.ф. $U$ разрешимы множества (*T-предикаты*):
  #eq[
    $T' = {(n, x, y, k) | U "останавливается на входе" (n, x) "за" k "шагов и выводит" y} \
      T' = {(n, x, y) | U "останавливается на входе" (n, x) "за" k "шагов"}$
  ]
]

#proposition[
  Пусть $U$ -- у.в.ф. Тогда множество
  #eq[
    $K = {n in NN | exists k in NN : T(n, n, k)}$
  ]
  неразрешимо, но перечеслимо
]

#proof[
  Допустим $K$ разрешимо.

  Рассмотрим $f$:
  #eq[
    $f(n) tilde.eq cases(1\, n in.not K, "undef"\, n in K)$
  ]
  Она вычислима, так как $K$ разрешимо.

  Значит $exists m in NN : f = U_m$. В частности $f(m) tilde.eq U(m, m)$. Но
  - $m in K => f(m) "undef" => U(m, m) "undef" => m in.not K$
  - $m in.not K => f(m) = 1 => U(m, m) = 1 => m in K$
  Противоречие!
]

#definition[
  Вычислимая функция $U: NN^2 overset(->, p) NN$ называется *главной у.в.ф.*, если для любой вычислимой функции $V: NN^2 overset(->, p) NN$ найдётся вычислимая тотальная функция $S: NN -> NN$, такая, что
  #eq[
    $forall n in NN : U_(S(n)) = V_n$
  ]
]

#theorem("Клини")[
  Пусть $U$ -- г.у.в.ф. и вычислимая функция $f: NN -> NN$ тотальна.

  Тогда существует $n in NN$, такая что $U_n = U_(f(n))$
]

#theorem("О рекурсии")[
  Пусть $U$ -- г.у.в.ф., а $V: NN^2 -> NN$ -- вычислима.

  Тогда $exists n in NN : U_n = V_n$
]

#proof[
  Ввиду главности $U$ существует вычислимая тотальная $S: forall k in NN : U_(S(k)) = V_k$.

  А по теореме Клини $exists n: U_(S(n)) = U_n = V_n$
]

#theorem("Райса-Успенского")[
  Если семейство $cal(F)$ вычислимых функций нетривиально, то есть $emptyset != cal(F) != NN$, то его индексное множество 
  #eq[
    $F = {n in NN | U_n in cal(F)}$
  ]
  относительно любой г.у.в.ф. неразрешимо.
]

#proof[
  Предположим противное: пусть $F$ разрешимо, тогда вычислима тотальная функция
  #eq[
    $h(k) = cases(m\, k in F, n\, k in.not F)$
  ]
  где по аксиоме выбора $m$ -- индекс функции, которая не принадлежит $cal(F)$, а $n$ -- той, которая принадлежит.

  В таком случае можно применить теорему Клини:
  #eq[
    $exists t : U_t = U_(h(t))$
  ]
  Рассмотрим два случая
  - $t in F => U_t = U_(h(t)) in cal(F) => h(t) = m => U_m in.not cal(F)$ -- противоречие
  - $t in.not F => U_t = U_(h(t)) in.not cal(F) => h(t) = n => U_n in cal(F)$ -- противоречие

]