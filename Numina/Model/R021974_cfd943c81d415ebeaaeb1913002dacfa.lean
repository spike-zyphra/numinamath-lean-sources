import Mathlib

theorem algebra_287203 : (77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) +
    (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) = 7 := by

  have h1 : Real.sqrt 13 ^ 2 = 13 := by
    rw [Real.sq_sqrt]
    all_goals norm_num

  have h2 : (77 - 20 * Real.sqrt 13) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num)]

  have h3 : (77 + 20 * Real.sqrt 13) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num)]

  have h4 : (77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) = 7 := by

    have h5 : ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) ^ 3 = 77 - 20 * Real.sqrt 13 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num)]

    have h6 : ((77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) ^ 3 = 77 + 20 * Real.sqrt 13 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num)]

    have h7 : ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) * ((77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) = 9 := by
      have h8 : ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) * ((77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) = ((77 - 20 * Real.sqrt 13) * (77 + 20 * Real.sqrt 13)) ^ ((1 : ℝ) / 3) := by
        rw [← Real.mul_rpow]
        all_goals nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num)]

      rw [h8]

      have h9 : (77 - 20 * Real.sqrt 13) * (77 + 20 * Real.sqrt 13) = 729 := by
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num)]

      rw [h9]

      have h10 : (729 : ℝ) ^ ((1 : ℝ) / 3) = (9 : ℝ) := by
        have h11 : (729 : ℝ) = (9 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [h11]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num

      rw [h10]

    have h11 : ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) ^ 3 = 154 + 27 * ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) := by
      calc
        ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) ^ 3 = ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) ^ 3 + ((77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) * ((77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3))) * ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) := by ring
        _ = (77 - 20 * Real.sqrt 13) + (77 + 20 * Real.sqrt 13) + 3 * ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) * ((77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3))) * ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) := by rw [h5, h6]
        _ = (77 - 20 * Real.sqrt 13) + (77 + 20 * Real.sqrt 13) + 3 * (9) * ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) := by rw [h7]
        _ = 154 + 27 * ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)) := by
          nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num)]

    have h12 : ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) - 7) * (( (77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) ) ^ 2 + 7 * (( (77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) )) + 22 ) = 0 := by
      nlinarith [sq_nonneg (( (77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) + (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) ) - 7), sq_nonneg (( (77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) - (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) ) ), Real.sqrt_nonneg 13 ]

    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- Case $a + b - 7 = 0$.
      linarith
    · -- Case $(a + b)^2 + 7(a + b) + 22 = 0$.
      nlinarith [sq_nonneg ((77 - 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3) - (77 + 20 * Real.sqrt 13) ^ ((1 : ℝ) / 3)), Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ 0 by norm_num) ]

  exact h4