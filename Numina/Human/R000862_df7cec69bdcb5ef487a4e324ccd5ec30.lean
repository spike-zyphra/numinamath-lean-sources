import Mathlib

/-It takes Michael 0.30 hours to walk to school. How many seconds does it take him to walk to school?-/
theorem algebra_18680 {x : ℝ}(h : 0.30 * 3600 = x) : x = 1080 := by norm_num [← h]