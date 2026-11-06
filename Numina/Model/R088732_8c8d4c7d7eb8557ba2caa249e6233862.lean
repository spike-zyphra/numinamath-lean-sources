import Mathlib

theorem inequalities_83176 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x - Real.sqrt x ≤ y - 1 / 4) (h2 : y - 1 / 4 ≤ x + Real.sqrt x) :
    y - Real.sqrt y ≤ x - 1 / 4 ∧ x - 1 / 4 ≤ y + Real.sqrt y := by
  have h1' : (Real.sqrt y - 1 / 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h_a : y - Real.sqrt y ≤ x - 1 / 4 := by
    nlinarith [sq_nonneg (Real.sqrt x - 1 / 2), sq_nonneg (Real.sqrt y - 1 / 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith),
      Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      h1, h2]
  have h_b : x - 1 / 4 ≤ y + Real.sqrt y := by
    nlinarith [sq_nonneg (Real.sqrt x - 1 / 2), sq_nonneg (Real.sqrt y - 1 / 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith),
      Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      h1, h2]
  exact ⟨h_a, h_b⟩