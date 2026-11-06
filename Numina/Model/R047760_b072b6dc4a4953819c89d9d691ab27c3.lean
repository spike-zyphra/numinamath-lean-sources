import Mathlib

open Real

theorem algebra_244440 {x y z : ℝ}
    (hx : x = sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7))
    (hy : y = sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3))
    (hz : z = sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) :
    x * y * z = 12 := by
  rw [hx, hy, hz]
  have h1 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) = 12 := by
    have h2 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) ^ 2 = 6 := by
      have h3 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) ^ 2 = (sqrt (12 - 3 * sqrt 7)) ^ 2 + (sqrt (12 + 3 * sqrt 7)) ^ 2 - 2 * (sqrt (12 - 3 * sqrt 7) * sqrt (12 + 3 * sqrt 7)) := by
        ring
      rw [h3]
      have h4 : (sqrt (12 - 3 * sqrt 7)) ^ 2 = 12 - 3 * sqrt 7 := by
        apply Real.sq_sqrt
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      have h5 : (sqrt (12 + 3 * sqrt 7)) ^ 2 = 12 + 3 * sqrt 7 := by
        apply Real.sq_sqrt
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      have h6 : sqrt (12 - 3 * sqrt 7) * sqrt (12 + 3 * sqrt 7) = 9 := by
        calc
          sqrt (12 - 3 * sqrt 7) * sqrt (12 + 3 * sqrt 7) = sqrt ((12 - 3 * sqrt 7) * (12 + 3 * sqrt 7)) := by
            rw [← Real.sqrt_mul (by
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            )]
          _ = sqrt (81 : ℝ) := by
            have h11 : (12 - 3 * sqrt 7 : ℝ) * (12 + 3 * sqrt 7) = 81 := by
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            rw [h11]
          _ = (9 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h4, h5, h6]
    have h3 : (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) ^ 2 = 12 := by
      have h4 : (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) ^ 2 = (sqrt (7 - 4 * sqrt 3)) ^ 2 + (sqrt (7 + 4 * sqrt 3)) ^ 2 - 2 * (sqrt (7 - 4 * sqrt 3) * sqrt (7 + 4 * sqrt 3)) := by
        ring
      rw [h4]
      have h5 : (sqrt (7 - 4 * sqrt 3)) ^ 2 = 7 - 4 * sqrt 3 := by
        apply Real.sq_sqrt
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h6 : (sqrt (7 + 4 * sqrt 3)) ^ 2 = 7 + 4 * sqrt 3 := by
        apply Real.sq_sqrt
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h7 : sqrt (7 - 4 * sqrt 3) * sqrt (7 + 4 * sqrt 3) = 1 := by
        calc
          sqrt (7 - 4 * sqrt 3) * sqrt (7 + 4 * sqrt 3) = sqrt ((7 - 4 * sqrt 3) * (7 + 4 * sqrt 3)) := by
            rw [← Real.sqrt_mul (by
              nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
            )]
          _ = sqrt (1 : ℝ) := by
            have h11 : (7 - 4 * sqrt 3 : ℝ) * (7 + 4 * sqrt 3) = 1 := by
              nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
            rw [h11]
          _ = (1 : ℝ) := by
            simp
      nlinarith [h5, h6, h7]
    have h4 : (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ^ 2 = 2 := by
      have h5 : (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ^ 2 = (sqrt (2 + sqrt 3)) ^ 2 + (sqrt (2 - sqrt 3)) ^ 2 - 2 * (sqrt (2 + sqrt 3) * sqrt (2 - sqrt 3)) := by
        ring
      rw [h5]
      have h6 : (sqrt (2 + sqrt 3)) ^ 2 = 2 + sqrt 3 := by
        apply Real.sq_sqrt
        positivity
      have h7 : (sqrt (2 - sqrt 3)) ^ 2 = 2 - sqrt 3 := by
        apply Real.sq_sqrt
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h8 : sqrt (2 + sqrt 3) * sqrt (2 - sqrt 3) = 1 := by
        calc
          sqrt (2 + sqrt 3) * sqrt (2 - sqrt 3) = sqrt ((2 + sqrt 3) * (2 - sqrt 3)) := by
            rw [← Real.sqrt_mul (by
              nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
            )]
          _ = sqrt (1 : ℝ) := by
            have h11 : (2 + sqrt 3 : ℝ) * (2 - sqrt 3) = 1 := by
              nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
            rw [h11]
          _ = (1 : ℝ) := by
            simp
      nlinarith [h6, h7, h8]
    have h5 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) < 0 := by 
      have h6 : sqrt (12 - 3 * sqrt 7) < sqrt (12 + 3 * sqrt 7) := by
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      linarith
    have h7 : (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) < 0 := by 
      have h8 : sqrt (7 - 4 * sqrt 3) < sqrt (7 + 4 * sqrt 3) := by
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith
    have h8 : (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) > 0 := by
      have h9 : sqrt (2 + sqrt 3) > sqrt (2 - sqrt 3) := by
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith
    have h14 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) > 0 := by
      have h15 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) < 0 := by
        linarith [h5]
      have h16 : (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) < 0 := by
        linarith [h7]
      have h17 : (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) > 0 := by
        linarith [h8]
      have h18 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) > 0 := by
        apply mul_pos_of_neg_of_neg
        all_goals linarith 
      have h19 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) > 0 := by 
        apply mul_pos 
        linarith 
        all_goals linarith 
      linarith
    have h8' : ((sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) ^ 2 = 144 := by
      calc
        ((sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) ^ 2
          = ((sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) ^ 2) * ((sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) ^ 2) * ((sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ^ 2) := by 
            ring_nf
        _ = (6 : ℝ) * (12 : ℝ) * (2 : ℝ) := by 
          rw [h2, h3, h4]
        _ = (144 : ℝ) := by 
          norm_num
    have h51 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) = 12 := by
      have h81 : ((sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) ^ 2 = 144 := h8'
      have h12 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ≥ 0 := by 
        linarith [h14]
      have h13 : sqrt (( (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) ^ 2) = (12 : ℝ) := by
        have h14' : ((sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) ^ 2 = (144 : ℝ) := h8'
        have h15 : sqrt (( (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) ^ 2) = sqrt (144 : ℝ) := by
          rw [h14']
        have h16 : sqrt (144 : ℝ) = (12 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith
      have h14 : (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) = 12 := by
        have h15 : sqrt (( (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) ^ 2) = (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) := by
          rw [Real.sqrt_sq (show 0 ≤ ( (sqrt (12 - 3 * sqrt 7) - sqrt (12 + 3 * sqrt 7)) * (sqrt (7 - 4 * sqrt 3) - sqrt (7 + 4 * sqrt 3)) * (sqrt (2 + sqrt 3) - sqrt (2 - sqrt 3)) ) by linarith)]
        nlinarith [h13, h15]
      linarith 
    linarith 
  linarith [h1]