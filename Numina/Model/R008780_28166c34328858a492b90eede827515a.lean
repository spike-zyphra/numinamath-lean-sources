import Mathlib
open Real

theorem algebra_96968 (f : ℝ → ℝ → ℝ → ℝ) (hf : ∀ a b c, f a b c = (c + a) / (c - b)) :
f 1 (-2) (-3) = 2 := by 
  rw [hf]
  norm_num