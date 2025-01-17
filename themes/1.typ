#import "../conf.typ": *

== Включение и равенство множеств. Основные способы задания множеств. Операции и основные тождества алгебры множеств. Упорядоченные пары и декартово произведение.

#definition[
  Множество $A$ *включено* $subset.eq$ в множество $B <=>$
  #eq[
    $x in A => x in B$
  ]
]

#definition[
  Множество $A$ *равно* множеству $B <=>$
  #eq[
    $x in A <=> x in B$
  ]
]

#lemma("Свойства включения")[
  - $A subset.eq A$
  - $A subset.eq B and B subset.eq C => A subset.eq C$
  - $A = B <=> A subset.eq B and B subset.eq A$
]

#lemma("Свойства равенства")[
  - $A = A$
  - $A = B and B = C => A = C$
  - $A = B => B = A$
]

#note("Основные способы задания множеств")[
  - Назвать все его элементы, когда число этих элементов конечно и все они уже определены
  - Выделение всех элементов какого-нибудь уже определённого множества $A$, обладающих некоторым точно определённым свойством $phi$
  - Рассмотреть *множество всех подмножеств* множества $A$. Такое множество обозначают выражением $cal(P)(A)$
  - Располагая каким-нибудь множеством $X$, рассмотреть его объединение, обозначаемое $union X$ и состоящее из всевозможных элементов множеств, принадлежащих $X$
]

#definition[
  *Объединением* множеств $A$ и $B$ называется множество $A union B$:
  #eq[
    $x in A union B <=> x in A or x in B$
  ]
]

#definition[
  *Пересечением* множеств $A$ и $B$ называется множество $A sect B$:
  #eq[
    $x in A sect B <=> x in A and x in B$
  ]
]

#definition[
  *Разностью* множеств $A$ и $B$ называется множество $A without B$:
  #eq[
    $x in A without B <=> x in A and x in.not B$
  ]
]

#definition[
  Нередвко все рассматриваемые множества оказываются подмножествами какого-нибудь множества $U$.

  Такое $U$ называют тогда *универсумом*.

  Для каждого подмножества $A$ заданного универсума $U$ определено *дополнение*
  #eq[
    $overline(A) = U without A$
  ]
]

#theorem("Основные тождества алгебры множеств")[
  $forall A, B, C$ и любого включающего их универсума $U$ верно:
  - $A sect B = B sect A; A union B = B union A$
  - $(A sect B) sect C = A sect (B sect C); (A union B) union C = A union (B union C)$
  - $A sect A = A; A union A = A$
  - $A sect (A union B) = A; A union (A sect B) = A$
  - $overline(overline(A)) = A$
  - $A sect (B union C) = (A sect B) union (A sect C); A union (B sect C) = (A union B) sect (A union C)$
  - $overline(A sect B) = overline(A) union overline(B); overline(A union B) = overline(A) sect overline(B)$
  - $A sect emptyset = emptyset; A union emptyset = A; A sect U = A; A union U = U; overline(emptyset) = U; overline(U) = emptyset$
  - $A sect overline(A) = emptyset; A union overline(A) = U$
]

#definition[
  Для произвольных множеств $a$ и $b$ символом $(a, b)$ обозначают множество ${{a}, {b, c}}$, называемое *упорядоченной парой* множеств $a$ и $b$
]

#definition[
  *Декартовым (или прямым)* произведением множеств $A$ и $B$ называется множество
  #eq[
    $A times B = {z in cal(P)(cal(P)(A union B)) | exists a in A : exists b in B : z = (a, b)}$
  ]
]
