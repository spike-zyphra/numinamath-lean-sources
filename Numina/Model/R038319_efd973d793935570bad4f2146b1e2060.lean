import Mathlib

theorem algebra_195641 : {x : ℝ | 64 * x ^ 3 - 24 * x ^ 2 - 6 * x + 1 = 0} = {1/8, -1/4, 1/2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, show that if $x$ is a root, then $x \in \{-1/4, 1/8, 1/2\}$.
    intro h
    have h1 : 64 * x ^ 3 - 24 * x ^ 2 - 6 * x + 1 = 0 := h
    have h2 : (x - 1/8) * (x + 1/4) * (x - 1/2) = 0 := by 
      nlinarith [sq_nonneg (x - 1/8), sq_nonneg (x + 1/4), sq_nonneg (x - 1/2), h1]
    cases' (mul_eq_zero.1 h2) with h3 h4
    cases' (mul_eq_zero.1 h3) with h5 h6
    · -- Case where $x - 1/8 = 0$
      left
      linarith
    · -- Case where $x + 1/4 = 0$
      right
      left
      linarith
    · -- Case where $x - 1/2 = 0$
      right
      right
      linarith
  · -- Now show the reverse: each element in the set is a root.
    rintro (h | h | h)
    · -- Case where $x = 1/8$
      rw [h]
      norm_num
    · -- Case where $x = -1/4$
      rw [h]
      norm_num
    · -- Case where $x = 1/2$
      rw [h]
      norm_num