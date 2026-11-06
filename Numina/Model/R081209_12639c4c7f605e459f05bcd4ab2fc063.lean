import Mathlib

theorem algebra_216635 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : y = 13.5 - 9 * x) (h2 : -y = 24 - 1.5 * x ^ 2) :
    (x + y) / 24 = 0.2 := by 
  have eq1 : y = 13.5 - 9 * x := h1
  have eq2 : -y = 24 - 1.5 * x ^ 2 := h2
  have eq3 : 1.5 * x ^ 2 + 9 * x - 37.5 = 0 := by 
    rw [show -y = -(13.5 - 9 * x) by rw [eq1]] at eq2
    nlinarith
  have eq4 : 3 * x ^ 2 + 18 * x - 75 = 0 := by
    ring_nf at eq3 ⊢
    nlinarith
  have eq5 : x^2 + 6 * x - 25 = 0 := by
    nlinarith
  have hx2 : x = (-6 + Real.sqrt 136) / 2 ∨ x = (-6 - Real.sqrt 136) / 2 := by
    have h : x^2 + 6 * x - 25 = 0 := eq5
    have : (x - (-6 + Real.sqrt 136) / 2) * (x - (-6 - Real.sqrt 136) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (136 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (136 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp this) with h1 h2
    · left
      linarith
    · right
      linarith
  cases' hx2 with hx1 hx2
  · -- Case where x is positive root
    have hx3 : x = (-6 + Real.sqrt 136) / 2 := hx1
    have h3 : x + y = 4.8 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (136 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (136 : ℝ) by norm_num)]
    linarith
  · -- Case where x is negative root
    have hx3 : x = (-6 - Real.sqrt 136) / 2 := hx2
    have h4 : x < 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (136 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (136 : ℝ) by norm_num)]
    linarith