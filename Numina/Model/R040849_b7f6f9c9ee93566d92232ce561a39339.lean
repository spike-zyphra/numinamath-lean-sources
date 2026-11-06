import Mathlib

theorem inequalities_600796 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 3) :
    Real.sqrt x / (2 * x + 3) + Real.sqrt y / (2 * y + 3) + Real.sqrt z / (2 * z + 3) ≤ 3 / 5 := by

  have h1 : ∀ x : ℝ, 0 < x → Real.sqrt x / (2 * x + 3) ≤ (1 / 50) * x + 9 / 50 := by
    intro x hx
    have h2 : 0 < 2 * x + 3 := by linarith
    apply (div_le_iff₀ h2).mpr
    nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (x - 1), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
      sq_nonneg (Real.sqrt x - (x + 9)), 
      sq_nonneg (2 * x + 3 - 25), 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x), 
      Real.sqrt_nonneg x, 
      mul_nonneg (show (0 : ℝ) ≤ (x) by linarith) (show (0 : ℝ) ≤ Real.sqrt x by positivity)]
  
  have h2 := h1 x hx
  have h3 := h1 y hy
  have h4 := h1 z hz

  linarith [h2, h3, h4, h]