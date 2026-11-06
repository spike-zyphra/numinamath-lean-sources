import Mathlib

theorem algebra_123400 (a b c d : ℝ) (ha : 0 < a) (hd : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b)
    (hba : b ≤ a) (h₀ : a + b + c + d = 4) (h₁ : a^2 + b^2 + c^2 + d^2 = 8) :
    a ≤ 1 + Real.sqrt 3 := by
  have h2 : b + c + d = 4 - a := by linarith
  have h3 : b^2 + c^2 + d^2 = 8 - a^2 := by linarith
  have h4 : (b + c + d) ^2 ≤ 3 * (b^2 + c^2 + d^2) := by 
    linarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  rw [h2, h3] at h4
  have h5 : 4 * a^2 - 8 * a - 8 ≤ 0 := by
    nlinarith
  have h6 : a ^ 2 - 2 * a - 2 ≤ 0 := by
    nlinarith
  have h7 : a ≤ 1 + Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sqrt_pos.mpr (show 0 < 3 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
  exact h7