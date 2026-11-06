import Mathlib


/-
Call admissible a set $A$ of integers that has the following property:  $$ \text { If } x, y \in A \text { (possibly } x=y \text { ) then } x^{2}+k x y+y^{2} \in A \text { for every integer } k \text {. } $$  Determine all pairs $m, n$ of nonzero integers such that the only admissible set containing both $m$ and $n$ is the set of all integers.
-/
theorem N1
    (admissible : Set ℤ → Prop)
    (h_admissible : ∀ A, admissible A = ∀ x ∈ A, ∀ y ∈ A, ∀ k : ℤ,  x ^ 2 + k * x * y + y ^ 2 ∈ A)
    (m n : ℤ)
    (h_m_nonzero : m ≠ 0)
    (h_n_nonzero : n ≠ 0) :
    (∀ A, m ∈ A ∧ n ∈ A ∧ admissible A ↔ A = Set.univ) ↔ m.gcd n = 1 := by

  -- The set  $$ A=\{\ldots,-2 d,-d, 0, d, 2 d, \ldots\} $$ is admissible, because if $d$ divides $x$ and $y$ then it divides $x^{2}+k x y+y^{2}$ for every integer $k$.
  have l_0 (m n : ℤ) :
      admissible {x : ℤ | ∃ k, x = k * m.gcd n} ∧
      m ∈ {x : ℤ | ∃ k, x = k * m.gcd n} ∧
      n ∈ {x : ℤ | ∃ k, x = k * m.gcd n} := by
    set d := m.gcd n
    constructor
    . rw [h_admissible]
      intro x ⟨u, hu⟩ y ⟨v, hv⟩ k
      use d * (u ^ 2 + k * u * v + v ^ 2)
      rw [hu, hv]
      ring
    . dsimp
      constructor
      . use m / d
        rw [Int.ediv_mul_cancel Int.gcd_dvd_left]
      . use n / d
        rw [Int.ediv_mul_cancel Int.gcd_dvd_right]

  -- (i) $k x^{2} \in A$ for every $x \in A$ and every integer $k$.
  -- To justify (i) let $y=x$ in the definition of an admissible set.
  have l_1 (A : Set ℤ) (hA : admissible A) :
      ∀ x ∈ A, ∀ k : ℤ, k * x ^ 2 ∈ A := by
    intro x hx k
    rw [h_admissible] at hA
    specialize hA x hx x hx (k - 2)
    rw [mul_assoc, ← pow_two, add_right_comm, ← two_mul, ← add_mul, add_sub_cancel] at hA
    exact hA

  -- (ii) $(x+y)^{2} \in A$ for all $x, y \in A$.
  -- To justify (ii) let $k=2$.
  have l_2 (A : Set ℤ) (hA : admissible A) :
      ∀ x ∈ A, ∀ y ∈ A, (x + y) ^ 2 ∈ A := by
    intro x hx y hy
    rw [h_admissible] at hA
    specialize hA x  hx y hy 2
    convert hA
    ring

  set d := m.gcd n

  obtain ⟨r0, hm0, hn0⟩ := l_0 m n
  set s0 := {x : ℤ | ∃ k, x = k * d}

  constructor
  -- if the only admissible set containing both $m$ and $n$ is the set of all integers, then d = 1
  . intro h
    specialize h s0
    simp only [hm0, hn0, r0, true_and, true_iff, s0] at h
    apply Set.univ_subset_iff.mpr at h

    have this : ∀ t ∈ Set.univ, t ∈ {x : ℤ | ∃ k, x = k * d} := fun t a => h a

    specialize this 1 trivial
    dsimp at this
    obtain ⟨k, hk⟩ := this

    by_contra! h_contra
    rcases eq_or_ne k 0 with h1 | _
    . rw [h1, zero_mul] at hk
      contradiction
    . zify at h_contra
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hk.symm with ⟨_, hdv⟩ | ⟨_, hdv⟩
      <;> contradiction

  -- if d = 1, then the only admissible set containing both $m$ and $n$ is the set of all integers
  . intro h_d_eq_one A
    constructor
    . intro ⟨hm, hn, hA⟩

      -- Since $\operatorname{gcd}(m, n)=1$, we also have $\operatorname{gcd}\left(m^{2}, n^{2}\right)=1$. Hence one can find integers $a, b$ such that $a m^{2}+b n^{2}=1$.
      have : ∃ a b, a * m ^ 2 + b * n ^ 2 = 1 := by
        apply IsCoprime.pow
        exact Int.isCoprime_iff_gcd_eq_one.mpr h_d_eq_one
      obtain ⟨a, b, hab⟩ := this

      -- It follows from (i) that $a m^{2} \in A$ and $b n^{2} \in A$.
      have t1 : a * m ^ 2 ∈ A :=
        l_1 A hA m hm a

      have t2 : b * n ^ 2 ∈ A :=
        l_1 A hA n hn b

      -- Now we deduce from (ii) that $1=\left(a m^{2}+b n^{2}\right)^{2} \in A$.
      have t3 : (a * m ^ 2 + b * n ^ 2) ^ 2 ∈ A :=
        l_2 A hA (a * m ^ 2) t1 (b * n ^ 2) t2
      rw [hab, one_pow] at t3

      -- if $1 \in A$ then (i) implies $k \in A$ for every integer $k$.
      apply Set.eq_univ_of_univ_subset
      intro k _
      convert l_1 A hA 1 t3 k
      ring

    . simp_all only [eq_iff_iff, ne_eq, Set.mem_setOf_eq, forall_exists_index, Set.mem_univ,
      implies_true, imp_self, and_self]
