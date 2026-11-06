import Mathlib

open Real

theorem algebra_4922 : √(26 + 2 * √(105)) = √21 + √5 := by
  have h1 : (Real.sqrt 21 + Real.sqrt 5) ^ 2 = 26 + 2 * Real.sqrt (105) := by
    calc
      (Real.sqrt 21 + Real.sqrt 5) ^ 2 = (Real.sqrt 21) ^ 2 + (Real.sqrt 5) ^ 2 + 2 * (Real.sqrt 21 * Real.sqrt 5) := by ring
      _ = 21 + 5 + 2 * (Real.sqrt 21 * Real.sqrt 5) := by
        have h2 : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
        have h3 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        rw [h2, h3]
        all_goals ring
      _ = 26 + 2 * (Real.sqrt 21 * Real.sqrt 5) := by ring
      _ = 26 + 2 * Real.sqrt (105) := by
        have h4 : Real.sqrt 21 * Real.sqrt 5 = Real.sqrt (105) := by
          rw [← Real.sqrt_mul (by norm_num)]
          all_goals norm_num
          all_goals norm_num
        rw [h4]
  have h2 : Real.sqrt (26 + 2 * Real.sqrt (105)) = Real.sqrt ((Real.sqrt 21 + Real.sqrt 5) ^ 2) := by
    rw [h1]
  rw [h2]
  have h3 : Real.sqrt ((Real.sqrt 21 + Real.sqrt 5) ^ 2) = Real.sqrt 21 + Real.sqrt 5 := by
    rw [Real.sqrt_sq (show 0 ≤ Real.sqrt 21 + Real.sqrt 5 by positivity)]
  exact h3