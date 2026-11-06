import Mathlib

theorem calculus_147864 (φ : ℝ → ℝ) (hφ : ∀ x, ∫ t in Set.Ioo 0 x, Real.exp (x - t) * φ t = x) :
    φ = fun x => 1 - x := by
  have h1 := hφ (-1 : ℝ)
  norm_num [Set.mem_Ioo] at h1 
  all_goals linarith