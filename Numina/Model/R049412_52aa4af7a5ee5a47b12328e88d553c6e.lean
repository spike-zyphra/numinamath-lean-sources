import Mathlib

theorem calculus_12537 : (fun a b c d : ℝ => !![a, b; c, d]) 3 0 1 2 + (fun a b c d : ℝ => !![a, b; c, d]) (-5) (-7) 4 (-9) = (fun a b c d : ℝ => !![a, b; c, d]) (-2) (-7) 5 (-7) := by 
  norm_num [Matrix.ext_iff]
  all_goals norm_num