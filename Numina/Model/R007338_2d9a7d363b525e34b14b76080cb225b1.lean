import Mathlib

def diamond (x y : ℝ) := |x - y|

theorem algebra_93849 : (diamond 1 (diamond 2 3)) - diamond (diamond 1 2) 3 = -2 := by
  dsimp [diamond]
  norm_num [abs_of_nonneg, abs_of_nonpos]