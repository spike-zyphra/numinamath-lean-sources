import Mathlib

theorem algebra_9230 {f : ℝ → ℝ} (hf : StrictAntiOn f (Set.Ioi 0)) :
    f 3 < f 2 := by 
  apply hf
  all_goals norm_num