import Mathlib

theorem algebra_18797:
  {x : ℝ | x^2 + 4 * x ≠ 0 ∧ x - 1 ≠ 0 ∧ (x ^ 2 + 4 * x) / (x - 1) + (72 * x - 72) / (x ^ 2 + 4 * x) - 18 = 0} = {2, 6} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Assume x is in the solution set, prove x ∈ {2, 6}.
    rintro ⟨h1, h2, h3⟩
    have eq2 : (x ^ 2 + 4 * x) / (x - 1) + (72 * x - 72) / (x ^ 2 + 4 * x) = 18 := by linarith
    have eq4 : (x ^ 2 + 4 * x) ^ 2 + (72 * x - 72) * (x - 1) = 18 * (x ^ 2 + 4 * x) * (x - 1) := by
      have h6 : x^2 + 4 * x ≠ 0 := h1
      have h7 : x - 1 ≠ 0 := h2
      field_simp [(show x^2 + 4 * x ≠ 0 by exact h1), (show x - 1 ≠ 0 by exact h2)] at eq2 ⊢
      nlinarith [sq_pos_of_ne_zero (show x ^ 2 + 4 * x ≠ 0 by exact h1), sq_pos_of_ne_zero (show x - 1 ≠ 0 by exact h2)]
    have h8 : (x - 2) * (x - 6) = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 6), sq_pos_of_ne_zero (show x ^ 2 + 4 * x ≠ 0 by exact h1), sq_pos_of_ne_zero (show x - 1 ≠ 0 by exact h2)]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case where x - 2 = 0, so x = 2
      left
      linarith
    · -- Case where x - 6 = 0, so x = 6
      right
      linarith
  · -- Show that 2 and 6 satisfy the equation.
    rintro (rfl | rfl)
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num