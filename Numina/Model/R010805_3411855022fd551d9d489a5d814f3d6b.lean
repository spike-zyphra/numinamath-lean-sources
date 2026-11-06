import Mathlib

theorem algebra_9227 {f g : ℝ → ℝ} (hf : f = fun x => x ^ 2) (hg : g = fun x => x + 2) :
    f (g 3) = 25 := by 
  rw [hg, hf]
  norm_num