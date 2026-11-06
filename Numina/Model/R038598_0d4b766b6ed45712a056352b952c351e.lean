import Mathlib

theorem algebra_22328 : {n : ℤ | 3 * n ^ 3 - 12 * n = 0}.ncard = 3 := by
  have h1 : {n : ℤ | 3 * n ^ 3 - 12 * n = 0} = {-2, 0, 2} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, show that if $3n^3-12n = 0$, then $n \in \{-2, 0, 2\}$.
      intro h
      have eq1 : 3 * n * (n - 2) * (n + 2) = 0 := by
        linarith [h]
      cases' (mul_eq_zero.mp eq1) with h2 h3
      · cases' (mul_eq_zero.mp h2) with h4 h5
        · -- Case $3n = 0$, so $n = 0$.
          have hn : n = 0 := by
            nlinarith
          simp [hn]
        · -- Case $n - 2 = 0$, so $n = 2$.
          have hn : n = 2 := by
            linarith
          simp [hn]
      · -- Case $n + 2 = 0$, so $n = -2$.
        have hn : n = -2 := by
          linarith
        simp [hn]
    · -- Now, show the reverse: if $n \in \{-2, 0, 2\}$, then $3n^3-12n = 0$.
      rintro (rfl | rfl | rfl)
      · -- For $n = -2$.
        norm_num
      · -- For $n = 0$.
        norm_num
      · -- For $n = 2$.
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp