import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20754 :
  IsLeast {y : ℝ | ∃ x > 0, y = ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3))} 6 := by
  constructor
  · -- Prove 6 is in the set.
    use 1
    norm_num
  · -- Prove 6 is the minimum.
    intro y hy
    rcases hy with ⟨x, hx_pos, hy_eq⟩
    have eq1 : ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) = 3 * (x + 1 / x) := by
      have hx1 : x ≠ 0 := by linarith
      field_simp [hx1]
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg (x - 1)]
    have hy_eq' : y = 3 * (x + 1 / x) := by
      rw [hy_eq]
      rw [eq1]
    have h2 : x + 1 / x ≥ 2 := by
      have h3 : x > 0 := hx_pos
      have h4 : x + 1 / x - 2 ≥ 0 := by
        have h5 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
          field_simp
          ring
        rw [h5]
        have h6 : (x - 1) ^ 2 ≥ 0 := by nlinarith
        have h7 : x > 0 := hx_pos
        positivity
      linarith
    have h3 : 3 * (x + 1 / x) ≥ 6 := by
      nlinarith
    have h4 : y ≥ 6 := by
      linarith [hy_eq', h3]
    linarith