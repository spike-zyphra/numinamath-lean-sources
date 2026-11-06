import Mathlib

open Real

theorem algebra_27 : sqrt ((1 - sqrt 2)^2) + (Real.pi - 3.14)^0 - 3 * sqrt (1 / 2) = -sqrt 2 / 2 := by
  have h1 : sqrt ((1 - sqrt 2) ^ 2) = sqrt 2 - 1 := by
    have h1 : sqrt ((1 - sqrt 2) ^ 2) = |1 - sqrt 2| := by
      rw [Real.sqrt_sq_eq_abs]
    have h2 : 1 < sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    rw [h1, abs_of_neg (sub_neg_of_lt h2)]
    ring
  have h3 : (Real.pi - 3.14 : ℝ) ^ 0 = 1 := by
    simp
  have h4 : 3 * sqrt (1 / 2) = 3 / 2 * sqrt 2 := by
    calc
      3 * sqrt (1 / 2)
          = 3 * (sqrt 1 / sqrt 2) := by
            rw [show (1 / 2 : ℝ) = (1 : ℝ) / (2 : ℝ) by norm_num]
            field_simp [show (2 : ℝ) ≠ 0 by norm_num]
      _ = 3 * (1 / sqrt 2) := by simp
      _ = 3 / 2 * sqrt 2 := by
        field_simp [show (sqrt 2 : ℝ) ≠ 0 by
          have : 0 < sqrt 2 := Real.sqrt_pos.2 (show (0:ℝ)<2 by norm_num)
          linarith
        ]
        ring_nf
        norm_num
  rw [h1, h3, h4]
  ring_nf