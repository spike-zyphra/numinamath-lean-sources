import Mathlib

theorem algebra_309595 {x y : ℝ} (h₀ : x + y = 3) (h₁ : 1 / (x + y^2) + 1 / (x^2 + y) = 1 / 2) :
    x^5 + y^5 = 123 := by
  have h2 : x + y ^ 2 ≠ 0 := by
    by_contra h
    have h3 : 1 / (x + y ^ 2) = 0 := by
      rw [h]
      norm_num
    have h4 : 1 / (x ^ 2 + y) = 1 / 2 := by
      linarith [h₁, h3]
    field_simp at h4
    all_goals nlinarith
  have h8 : x ^ 2 + y ≠ 0 := by
    by_contra h
    have h7 : 1 / (x ^ 2 + y) = 0 := by
      rw [h]
      norm_num
    have h4 : 1 / (x + y ^ 2) = 1 / 2 := by
      linarith [h₁, h7]
    field_simp at h4
    all_goals nlinarith
  -- clear denominators in h₁
  have h3 : (x ^ 2 + y) + (x + y ^ 2) = (1 / 2) * (x + y ^ 2) * (x ^ 2 + y) := by
    field_simp [(show x + y ^ 2 ≠ 0 by exact h2), (show x ^ 2 + y ≠ 0 by exact h8)] at h₁ ⊢
    nlinarith
  have h4 : (x ^ 2 + y) + (x + y ^ 2) = 12 - 2 * (x * y) := by
    nlinarith [sq_nonneg (x - y), h₀]
  have h6 : 24 - 4 * (x * y : ℝ) = (x + y ^ 2) * (x ^ 2 + y) := by
    nlinarith [h4, h3, h₀, sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x * y - 3)]
  -- solve quadratic to solve value
  have h7 : (x * y - 1) * (x * y - 3) = 0 := by
    nlinarith [h6, sq_nonneg (x - y), h₀, sq_nonneg (x - (3 - x)), sq_nonneg (y - (3 - y)), sq_nonneg (x * y - 1), sq_nonneg (x * y - 3)]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- $x * y = 1$
    have h8 : x * y = 1 := by linarith
    have h9 : x ^ 5 + y ^ 5 = (x + y) ^ 5 - 5 * (x * y) * (x + y) ^ 3 + 5 * (x * y) ^ 2 * (x + y) := by
      ring_nf
    rw [h9, h₀, h8]
    norm_num
  · -- $x * y = 3$
    have h9 : x * y = 3 := by linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (3 - x)), sq_nonneg (y - (3 - y)), sq_nonneg (x * y - 3), sq_nonneg (x^2 + y^2 - 3)]
    all_goals nlinarith