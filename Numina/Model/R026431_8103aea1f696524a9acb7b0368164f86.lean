import Mathlib

theorem calculus_147774 (φ : ℝ → ℝ) (hφ : ∀ x, ∫ t in Set.Ioo 0 x, φ t * φ (x - t) = x ^ 3 / 6) :
    φ = (fun x => x) ∨ φ = (fun x => -x) := by 
  have h1 := hφ (-1)
  norm_num [Set.mem_Ioo] at h1
  all_goals linarith