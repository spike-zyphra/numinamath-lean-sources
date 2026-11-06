import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_286007 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x + 2 * y = 2 ∧ z = x ^ 2 / (2 * y) + 4 * y ^ 2 / x} 2 := by
  constructor
  · -- Show that 2 belongs to the set
    use 1, (0.5 : ℝ)
    norm_num
  · -- Show that 2 is a lower bound
    intro z hz
    rcases hz with ⟨x, y, hx, hy, h_eq, h_eq2⟩
    have h1 : x + 2 * y = 2 := h_eq
    have h5 : x ^ 2 / (2 * y) + 4 * y ^ 2 / x ≥ 2 := by
      have pos1 : 2 * y > 0 := by nlinarith
      have pos2 : x > 0 := by linarith
      have h6 : (x ^ 2 / (2 * y) + 4 * y ^ 2 / x - 2) ≥ 0 := by
        have h7 : (x ^ 2 / (2 * y) + 4 * y ^ 2 / x - 2) = (x ^ 3 + 8 * y ^ 3 - 4 * x * y) / (2 * x * y) := by
          field_simp
          ring
        rw [h7]
        apply div_nonneg
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - (1 / 2 : ℝ)), sq_nonneg (x - 2 * y), sq_nonneg (x * y), h_eq, mul_pos hx hy, sq_nonneg (x - 2 * y), sq_nonneg ((x - 1)^2), sq_nonneg ((y - (1 / 2))^2)]
        all_goals
          nlinarith
      linarith
    linarith [h_eq2, h5]