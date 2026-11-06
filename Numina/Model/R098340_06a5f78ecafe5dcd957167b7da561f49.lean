import Mathlib

theorem algebra_289610 :
    Set.ncard {x : ℝ | (x^2 - 4) * (x^2 - 1) = (x^2 + 3 * x + 2) * (x^2 - 8 * x + 7)} = 3 := by
  have h1 : {x : ℝ | (x^2 - 4) * (x^2 - 1) = (x^2 + 3 * x + 2) * (x^2 - 8 * x + 7)} = {-2, -1, 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward direction: If $(x^2 - 4)(x^2 - 1) = (x^2 + 3 x + 2)(x^2 - 8 x + 7)$, then $x \in \{-2, -1, 1\}$.
      intro hx
      have eq1 : (x^2 - 4) * (x^2 - 1) - ((x^2 + 3 * x + 2) * (x^2 - 8 * x + 7)) = 0 := by
        linarith [hx]
      have h2 : (x + 2) * (x + 1) * (x - 1) = 0 := by
        nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x + 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x - 2), sq_nonneg (x + 1)]
      cases' (mul_eq_zero.mp h2) with h3 h4
      cases' (mul_eq_zero.mp h3) with h5 h6
      · -- Case $x+2 = 0$, so $x = -2$.
        have hx1 : x = -2 := by linarith
        tauto
      · -- Case $x+1 = 0$, so $x = -1$.
        have hx2 : x = -1 := by linarith
        tauto
      · -- Case $x-1 = 0$, so $x = 1$.
        have hx3 : x = 1 := by linarith
        tauto
    · -- Backward direction: If $x \in \{-2, -1, 1\}$, then $(x^2 - 4)(x^2 - 1) = (x^2 + 3 x + 2)(x^2 - 8 x + 7)$.
      rintro (rfl | rfl | rfl)
      · -- $x = -2$
        norm_num
      · -- $x = -1$
        norm_num
      · -- $x = 1$
        norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]