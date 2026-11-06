import Mathlib

theorem algebra_283762 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 5 + a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e)
    (h1 : f 1 = 2017 * 1) (h2 : f 2 = 2017 * 2) (h3 : f 3 = 2017 * 3) (h4 : f 4 = 2017 * 4) :
    f 10 - f (-5) = 75615 := by
  have eq1 := hf 1
  have eq2 := hf 2
  have eq3 := hf 3
  have eq4 := hf 4
  have eq10 := hf 10
  have eq5 := hf (-5)
  simp only [eq1] at h1
  simp only [eq2] at h2
  simp only [eq3] at h3
  simp only [eq4] at h4
  simp only [eq10, eq5] 
  -- Compute f 10
  -- Compute f (-5)
  -- Simplify f 10 - f (-5)
  norm_num at h1 h2 h3 h4 ⊢
  linarith