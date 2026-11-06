import Mathlib

open Real

theorem algebra_251972 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : logb 10 x + logb 10 y = 1) (h2 : x^2 + y^2 - 3 * x - 3 * y = 8) :
    (x = 2 ∧ y = 5) ∨ (x = 5 ∧ y = 2) := by
  have h3 : logb 10 (x * y) = 1 := by
    rw [logb_mul (by linarith) (by linarith)]
    linarith [h1]
  have h4 : x * y = 10 := by
    have h5 : x * y > 0 := mul_pos hx hy
    have h6 : x * y = (10 : ℝ) ^ (logb 10 (x * y) : ℝ) := by
      field_simp [Real.rpow_logb, show x * y > 0 by linarith]
    rw [h3] at h6
    have h7 : (10 : ℝ) ^ ((1 : ℝ) : ℝ) = (10 : ℝ) := by
      norm_num
    rw [h7] at h6
    nlinarith
  have h5 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    nlinarith
  rw [h4] at h5
  have h6 : (x + y) ^ 2 - 3 * (x + y) - 28 = 0 := by
    nlinarith [h2, h5]
  have h7 : (x + y - 7) * (x + y + 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case $x + y = 7$:
    have h7' : x + y = 7 := by linarith
    have h8 : (x - 2) * (x - 5) = 0 := by
      nlinarith [h7', h4]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- x = 2:
      have hx2 : x = 2 := by linarith
      have hy5 : y = 5 := by linarith [h7', hx2]
      left
      exact ⟨hx2, hy5⟩
    · -- x = 5:
      have hx5 : x = 5 := by linarith
      have hy2 : y = 2 := by linarith [h7', hx5]
      right
      exact ⟨hx5, hy2⟩
  · -- Case $x + y = -4$:
    have h9' : x + y = -4 := by linarith
    nlinarith [h9', mul_pos hx hy]