import Mathlib

theorem algebra_86206 {a b c : ℝ} (h₀ : a ≤ b) (h₁ : b ≤ c)
    (h₂ : a + b + c = -1) (h₃ : a * b + b * c + a * c = -4) (h₄ : a * b * c = -2) :
    a = -1 - Real.sqrt 3 ∧ b = -1 + Real.sqrt 3 ∧ c = 1 := by

  have h5 : (a - 1) * (b - 1) * (c - 1) = 0 := by
    nlinarith [sq_nonneg (a + b + c + 1), sq_nonneg (a * b + b * c + a * c + 4), sq_nonneg (a * b * c + 2)]

  cases' (mul_eq_zero.mp h5) with h6 h7
  cases' (mul_eq_zero.mp h6) with h8 h9
  · -- Assume a = 1, which is a contradiction.
    nlinarith [sq_nonneg (b + 1), sq_nonneg (c + 1), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
  · -- Assume b = 1
    have h10 : a + c = -2 := by linarith
    have h11 : a * c = -2 := by
      have h12 : a * b + b * c + a * c = -4 := h₃
      rw [show b = 1 by linarith] at h12
      nlinarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (a + 1 - Real.sqrt 3), sq_nonneg (c + 1 + Real.sqrt 3), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  · -- Assume c = 1.
    have h14 : a + b = -2 := by linarith
    have h15 : a * b = -2 := by
      have h16 : a * b + b * c + a * c = -4 := h₃
      rw [show c = 1 by linarith] at h16
      nlinarith
    have h14' : (a - (-1 - Real.sqrt 3)) * (a - (-1 + Real.sqrt 3)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    cases' (mul_eq_zero.mp h14') with h17 h18
    · -- Assume a = -1 - sqrt(3)
      have ha : a = -1 - Real.sqrt 3 := by linarith
      have hb : b = -1 + Real.sqrt 3 := by nlinarith
      have hc : c = 1 := by nlinarith
      constructor
      · exact ha
      constructor
      · exact hb
      · exact hc
    · -- Assume a = -1 + sqrt(3)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (b + 1 + Real.sqrt 3), sq_nonneg (a - 1 - Real.sqrt 3)]