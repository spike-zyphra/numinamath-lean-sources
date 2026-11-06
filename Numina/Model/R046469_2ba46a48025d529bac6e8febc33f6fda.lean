import Mathlib

theorem algebra_11891 (a : ℕ → ℝ) (r : ℝ) (h₀ : ∀ n, a n = a 0 * r ^ n)
    (h₁ : 0 < a 0) (h₂ : 0 < r) (h₃ : 2 * a 4 + a 3 - 2 * a 2 - a 1 = 8) :
    2 * a 8 + a 7 ≥ 54 := by
  have ha4 : a 4 = a 0 * r ^ 4 := h₀ 4
  have ha3 : a 3 = a 0 * r ^ 3 := h₀ 3
  have ha2 : a 2 = a 0 * r ^ 2 :=  h₀ 2
  have ha1 : a 1 = a 0 * r ^ 1 := h₀ 1
  rw [ha4, ha3, ha2, ha1] at h₃
  have ha8 : a 8 = a 0 * r ^ 8 := h₀ 8
  have a7_eq : a 7 = a 0 * r ^ 7 := h₀ 7
  have h4 : 2 * a 8 + a 7 = a 0 * r ^ 7 * (2 * r + 1) := by
    rw [ha8, a7_eq]
    ring
  have h5 : a 0 * r * (2 * r ^ 3 + r ^ 2 - 2 * r - 1) = 8 := by
    nlinarith
  have h7 : r > 1 := by
    nlinarith [sq_nonneg (r - 1), sq_nonneg (r + 1), sq_nonneg (2 * r + 1), sq_nonneg (r ^ 2 - 1), 
        h₁, h₂, mul_pos h₁ h₂, mul_pos h₁ (show 0 < r ^ 2 by positivity), mul_pos h₁ (show 0 < r ^ 3 by positivity)]
  nlinarith [sq_nonneg (r ^ 2 - 3 / 2), sq_nonneg (a 0 * r ^ 3 - 3 * Real.sqrt (3 / 2) ^ 3), 
    sq_nonneg (a 0 * r ^ 2 - 3 * Real.sqrt (3 / 2) ^ 2), sq_nonneg (a 0 * r - 3 * Real.sqrt (3 / 2)), 
      sq_nonneg (a 0 - 3 * Real.sqrt (3 / 2)), sq_nonneg (r ^ 2 - 3 / 2), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < 3 / 2 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 2 by linarith), 
            h₁, h₂, mul_pos h₁ h₂, mul_pos h₁ (show 0 < r ^ 2 by positivity)]