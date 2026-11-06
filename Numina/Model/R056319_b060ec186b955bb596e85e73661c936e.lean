import Mathlib

theorem calculus_22722 : (fun a b c d : ℝ => !![a, b; c, d]) 1 5 (-2) 4 + (fun a b c d : ℝ => !![a, b; c, d]) 0 (-3) 8 (-5) = (fun a b c d : ℝ => !![a, b; c, d]) 1 2 6 (-1) := by 
  norm_num [Matrix.ext_iff]