import Mathlib

open Real

theorem inequalities_11019 (f : ℝ → ℝ) (h : ∀ x y z, f (x + y) + f (y + z) + f (z + x) ≥ 3 * f (x + 2 * y + z)) :
    f 1 - f 0 = 0 := by 
  have h1 := h 0 0 1
  norm_num at h1
  have h6 : f 1 ≤ f 0 := by 
    linarith [h1]
  have eq1 := h 0 0 (-1)
  norm_num at eq1
  have eq3 := h (-1) (0 : ℝ) 1
  norm_num at eq3
  have eq4 : f (-1) + f 1 ≥ 2 * f 0 := by
    linarith
  have eq5 : f (-1) ≤ f 0 := by 
    linarith [eq1]
  have eq6 : f 1 ≥ f 0 := by
    nlinarith [eq4, eq5]
  have eq7 : f 1 = f 0 := by
    linarith [h6, eq6]
  linarith [eq7]