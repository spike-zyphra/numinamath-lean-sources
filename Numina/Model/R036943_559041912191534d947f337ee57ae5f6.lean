import Mathlib

theorem algebra_304322 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a^2 + b^2 + c^2 = 1) :
    a * b * c ≤ Real.sqrt 6 / 18 := by
  have h2 : c = -a - b := by linarith
  rw [h2] at h₁
  have h3 : a^2 + b^2 + a * b = 1 / 2 := by
    nlinarith
  have h4 : a * b * c = - (a * b * (a + b)) := by
    rw [show c = -a - b by linarith]
    ring
  have h5 : a * b = (a + b) ^2 - 1 / 2 := by
    have eq1 : a^2 + b^2 + a * b = 1 / 2 := h3
    have eq2 : a^2 + b^2 = (a + b) ^2 - 2 * (a * b) := by
      nlinarith
    nlinarith
  have h6 : a * b * c = - ( (a + b) ^2 - 1 / 2 ) * (a + b) := by
    rw [h4]
    rw [h5]
    all_goals ring
  have h7 : - ( (a + b) ^2 - 1 / 2 ) * (a + b) ≤ Real.sqrt 6 / 18 := by
    nlinarith [sq_nonneg ((a + b) ^2 - 1 / 6), sq_nonneg ((a + b) - Real.sqrt 6 / 6), sq_nonneg ((a + b) + Real.sqrt 6 / 6), 
        Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), 
        sq_nonneg (a - b)
    ]
  have h8 : a * b * c = - ( (a + b) ^2 - 1 / 2 ) * (a + b) := h6
  linarith [h7, h8]