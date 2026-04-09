import TheoremDecomposer

/-- Простейшая конъюнкция: оба компонента — True.
    Декомпозиция тривиальна, но показывает базовый механизм:
    каждое слагаемое ∧ становится отдельной леммой. -/
theorem test_conj : True ∧ True := ⟨trivial, trivial⟩
#decompose_theorem test_conj

/-- Коммутативность конъюнкции.
    Классический пример ↔: декомпозиция даёт ровно два направления —
    прямое (mp) и обратное (mpr). -/
theorem test_iff (p q : Prop) : p ∧ q ↔ q ∧ p :=
  ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
#decompose_theorem test_iff

/-- Существование натурального числа, большего нуля.
    Декомпозиция ∃ оставляет утверждение целиком —
    пользователь сам предъявляет свидетеля (например, n = 1). -/
theorem test_exists : ∃ n : Nat, n > 0 := ⟨1, Nat.one_pos⟩
#decompose_theorem test_exists

/-- Импликационная цепочка: из трёх гипотез собираем конъюнкцию.
    Каждый компонент результата становится отдельной леммой
    с теми же гипотезами p → q → r →. -/
theorem test_impl (p q r : Prop) : p → q → r → p ∧ q ∧ r :=
  fun hp hq hr => ⟨hp, hq, hr⟩
#decompose_theorem test_impl

/-- Коммутативность и ассоциативность сложения натуральных чисел.
    Два фундаментальных свойства одновременно: декомпозиция показывает,
    что их можно доказывать независимо, а затем собрать через ⟨·, ·⟩. -/
theorem nat_comm_and_assoc (a b c : Nat) :
    a + b = b + a  ∧  (a + b) + c = a + (b + c) :=
  ⟨Nat.add_comm a b, Nat.add_assoc a b c⟩
#decompose_theorem nat_comm_and_assoc
#decompose_tree    nat_comm_and_assoc

/-- Монотонность сложения: если a ≤ b, то a + c ≤ b + c (с обеих сторон).
    Показывает симметричность — оба направления монотонности сразу. -/
theorem add_mono_both (a b c : Nat) (h : a ≤ b) :
    a + c ≤ b + c  ∧  c + a ≤ c + b :=
  ⟨Nat.add_le_add_right h c, Nat.add_le_add_left h c⟩
#decompose_theorem add_mono_both
#decompose_tree    add_mono_both

/-- Свойства нуля: он является левым и правым нейтральным элементом. -/
theorem zero_neutral (n : Nat) :
    0 + n = n  ∧  n + 0 = n :=
  ⟨Nat.zero_add n, Nat.add_zero n⟩
#decompose_theorem zero_neutral

/-- Оценка суммы: если каждое слагаемое ≤ bound, то сумма ≤ 2·bound.
    Демонстрирует работу с гипотезами-неравенствами. -/
theorem bounded_add (a b bound : Nat) :
    a ≤ bound → b ≤ bound →
    a + b ≤ 2 * bound  ∧  b + a ≤ 2 * bound :=
  fun ha hb => ⟨by omega, by omega⟩
#decompose_theorem bounded_add
#decompose_tree    bounded_add

/-- Свойства максимума: оба аргумента не превосходят max, и max симметричен.
    Тройная конъюнкция — пример A ∧ B ∧ C, где Lean парсит как A ∧ (B ∧ C). -/
theorem max_properties (a b : Nat) :
    a ≤ Nat.max a b  ∧  b ≤ Nat.max a b  ∧  Nat.max a b = Nat.max b a :=
  ⟨Nat.le_max_left a b, Nat.le_max_right a b, Nat.max_comm a b⟩
#decompose_theorem max_properties
#decompose_tree    max_properties

/-- Свойства минимума: min не превосходит оба аргумента. -/
theorem min_le_both (a b : Nat) :
    Nat.min a b ≤ a  ∧  Nat.min a b ≤ b :=
  ⟨Nat.min_le_left a b, Nat.min_le_right a b⟩
#decompose_theorem min_le_both

/-- Транзитивность делимости и делимость произведения.
    Если a∣b и b∣c, то не только a∣c, но и a∣bc. -/
theorem div_properties (a b c : Nat) (h1 : a ∣ b) (h2 : b ∣ c) :
    a ∣ c  ∧  a ∣ b * c :=
  ⟨Nat.dvd_trans h1 h2, Nat.dvd_mul_right_of_dvd h1 c⟩
#decompose_theorem div_properties
#decompose_tree    div_properties

/-- Делимость суммы: если a делит оба слагаемых, то делит и сумму. -/
theorem dvd_add_both (a b c : Nat) (h1 : a ∣ b) (h2 : a ∣ c) :
    a ∣ b + c  ∧  a ∣ c + b :=
  ⟨Nat.dvd_add h1 h2, Nat.dvd_add h2 h1⟩
#decompose_theorem dvd_add_both

/-- Чётность через ↔: два равносильных определения.
    ∃ k, n = 2*k эквивалентно 2∣n — классический пример ↔ с ∃ внутри. -/
theorem even_iff_exists (n : Nat) :
    (∃ k, n = 2 * k) ↔ (2 ∣ n) :=
  ⟨fun ⟨k, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, hk⟩⟩
#decompose_theorem even_iff_exists
#decompose_tree    even_iff_exists

/-- Позитивность и ненулевость — равносильные условия для Nat.
    Стандартная теорема из библиотеки, красивый пример ↔. -/
theorem pos_iff_ne_zero (n : Nat) : 0 < n ↔ n ≠ 0 :=
  Nat.pos_iff_ne_zero
#decompose_theorem pos_iff_ne_zero
#decompose_tree    pos_iff_ne_zero

/-- Рефлексивность ≤ равносильна рефлексивности =.
    Тривиально, но показывает симметрию ↔ на простом примере. -/
theorem le_iff_eq_of_refl (n : Nat) : n ≤ n ↔ n = n :=
  ⟨fun _ => rfl, fun _ => Nat.le_refl n⟩
#decompose_theorem le_iff_eq_of_refl

/-- Переход от строгого к нестрогому неравенству (↔ версия).
    Демонстрирует связь < и ≤ через эквивалентность. -/
theorem lt_iff_le_and_ne (a b : Nat) : a < b ↔ a ≤ b ∧ a ≠ b :=
  Nat.lt_iff_le_and_ne
#decompose_theorem lt_iff_le_and_ne
#decompose_tree    lt_iff_le_and_ne

/-- Транзитивность ≤ как цепочка: три неравенства дают четвёртое.
    Пример чистой цепочки A → B → C → D. -/
theorem le_chain (a b c d : Nat) :
    a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun h1 h2 h3 => Nat.le_trans (Nat.le_trans h1 h2) h3
#decompose_theorem le_chain
#decompose_tree    le_chain

/-- Из строгого неравенства и ≤ получаем два следствия одновременно. -/
theorem lt_le_consequences (a b c : Nat) :
    a < b → b ≤ c → a < c  ∧  a ≠ c :=
  fun h1 h2 =>
    let h := Nat.lt_of_lt_of_le h1 h2
    ⟨h, Nat.ne_of_lt h⟩
#decompose_theorem lt_le_consequences
#decompose_tree    lt_le_consequences

variable {V : Type} (Adj : V → V → Prop)

/-- Путь в графе: последовательность вершин, где каждые две
    соседние связаны ребром. Определяем индуктивно. -/
inductive Path (Adj : V → V → Prop) : V → V → Prop where
  | refl : ∀ v, Path Adj v v
  | step : ∀ u v w, Adj u v → Path Adj v w → Path Adj u w

/-- Достижимость: вершина w достижима из u, если существует путь. -/
def Reachable (Adj : V → V → Prop) (u w : V) : Prop :=
  Path Adj u w

/-- Рефлексивность достижимости: каждая вершина достижима из себя
    (путь нулевой длины). -/
theorem reachable_refl (v : V) : Reachable Adj v v :=
  Path.refl v
#decompose_theorem reachable_refl

/-- Транзитивность достижимости: если w достижима из u, а x из w,
    то x достижима из u. Это стандартное свойство отношения достижимости
    — оно транзитивно по построению через конкатенацию путей. -/
theorem reachable_trans (u w x : V)
    (h1 : Reachable Adj u w) (h2 : Reachable Adj w x) :
    Reachable Adj u x := by
  induction h1 with
  | refl _        => exact h2
  | step u v w' e p ih => exact Path.step u v x e (ih h2)
#decompose_theorem reachable_trans
#decompose_tree    reachable_trans

/-- Если есть ребро, то есть и путь длины 1.
    Единственный шаг через Path.step плюс рефлексия. -/
theorem edge_implies_reachable (u v : V) (h : Adj u v) :
    Reachable Adj u v :=
  Path.step u v v h (Path.refl v)
#decompose_theorem edge_implies_reachable

/-- Достижимость рефлексивна и транзитивна одновременно.
    Пример двойной конъюнкции на нетривиальном предикате. -/
theorem reachable_refl_and_trans (u v w : V)
    (h1 : Reachable Adj u v) (h2 : Reachable Adj v w) :
    Reachable Adj u u  ∧  Reachable Adj u w :=
  ⟨Path.refl u,
   reachable_trans Adj u v w h1 h2⟩
#decompose_theorem reachable_refl_and_trans
#decompose_tree    reachable_refl_and_trans

/-- Достижимость через промежуточную вершину:
    если u→v и v→w и w→x, то u→x и u→w.
    Пример цепочки транзитивности с двумя следствиями. -/
theorem reachable_chain (u v w x : V)
    (h1 : Reachable Adj u v)
    (h2 : Reachable Adj v w)
    (h3 : Reachable Adj w x) :
    Reachable Adj u x  ∧  Reachable Adj u w :=
  ⟨reachable_trans Adj u w x (reachable_trans Adj u v w h1 h2) h3,
   reachable_trans Adj u v w h1 h2⟩
#decompose_theorem reachable_chain
#decompose_tree    reachable_chain

/-- В неориентированном графе рёбра симметричны.
    Это отдельное свойство графа, не следующее из определения Adj. -/
def IsUndirected (Adj : V → V → Prop) : Prop :=
  ∀ u v, Adj u v → Adj v u

/-- В неориентированном графе достижимость симметрична:
    если w достижима из u, то u достижима из w.
    Доказывается индукцией по пути с разворотом каждого ребра. -/
theorem undirected_reachable_symm
    (hS : IsUndirected Adj) (u w : V)
    (h : Reachable Adj u w) :
    Reachable Adj w u := by
  induction h with
  | refl v        => exact Path.refl v
  | step u v w' e p ih =>
      exact reachable_trans Adj w' v u ih
              (edge_implies_reachable Adj v u (hS u v e))
#decompose_theorem undirected_reachable_symm
#decompose_tree    undirected_reachable_symm

/-- В неориентированном графе достижимость — отношение эквивалентности:
    рефлексивное, симметричное и транзитивное. -/
theorem reachable_equiv_undirected
    (hS : IsUndirected Adj) (u v w : V)
    (huv : Reachable Adj u v) (hvw : Reachable Adj v w) :
    Reachable Adj u w  ∧  Reachable Adj w u  ∧  Reachable Adj v u :=
  ⟨reachable_trans Adj u v w huv hvw,
   undirected_reachable_symm Adj hS u w
     (reachable_trans Adj u v w huv hvw),
   undirected_reachable_symm Adj hS u v huv⟩
#decompose_theorem reachable_equiv_undirected
#decompose_tree    reachable_equiv_undirected


/-- Граф связен, если любые две вершины взаимно достижимы. -/
def IsConnected (Adj : V → V → Prop) : Prop :=
  ∀ u v, Reachable Adj u v

/-- В связном графе для любых трёх вершин u, v, w
    выполняются оба: u→w и v→w.
    Декомпозиция даёт две независимые леммы о достижимости. -/
theorem connected_any_pair
    (hC : IsConnected Adj) (u v w : V) :
    Reachable Adj u w  ∧  Reachable Adj v w :=
  ⟨hC u w, hC v w⟩
#decompose_theorem connected_any_pair
#decompose_tree    connected_any_pair

/-- Связный неориентированный граф: достижимость работает в обе стороны
    для любой пары вершин. -/
theorem connected_undirected_both_ways
    (hC : IsConnected Adj) (hS : IsUndirected Adj) (u v : V) :
    Reachable Adj u v  ∧  Reachable Adj v u :=
  ⟨hC u v, undirected_reachable_symm Adj hS u v (hC u v)⟩
#decompose_theorem connected_undirected_both_ways
#decompose_tree    connected_undirected_both_ways
