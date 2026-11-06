import Mathlib

open Real

theorem algebra_6880 :
    sqrt (28 - 6 * sqrt 3) = 3 * sqrt 3 - 1 := by
  have h1 : (3 * sqrt 3 - 1) ^ 2 = 28 - 6 * sqrt 3 := by
      calc
          (3 * sqrt 3 - 1) ^ 2
              = (3 * sqrt 3) ^ 2 - 2 * (3 * sqrt 3) * 1 + 1 ^ 2 := by ring
          _ = 9 * (sqrt 3 * sqrt 3) - 6 * sqrt 3 + 1 := by ring
          _ = 9 * 3 - 6 * sqrt 3 + 1 := by rw [Real.mul_self_sqrt]; linarith [Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num)]
          _ = 27 - 6 * sqrt 3 + 1 := by ring
          _ = 28 - 6 * sqrt 3 := by ring

  have h2 : 0 ≤ 3 * sqrt 3 - 1 := by
      have h3 : sqrt 3 ≥ 1 := by
          have h4 : 1 < sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
          linarith
      linarith [h3]

  rw [←h1]
  field_simp [h2]