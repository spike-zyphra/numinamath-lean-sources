import Mathlib

open Real

theorem inequalities_153667 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (2 * x * y / (x + y) + sqrt ((x ^ 2 + y ^ 2) / 2)) ≥
    ((x + y) / 2 + sqrt (x * y)) := by 
  have h1 : 0 < x + y := by nlinarith
  have h4 : sqrt ((x ^ 2 + y ^ 2) / 2) ≥ 0 := by positivity
  have h5 : sqrt (x * y) ≥ 0 := by positivity

  have h7 : 0 ≤ (2 * x * y / (x + y) + sqrt ((x ^ 2 + y ^ 2) / 2)) - ((x + y) / 2 + sqrt (x * y)) := by
    have h8 : 0 < x + y := by linarith
    have h9 : (2 * x * y / (x + y) + sqrt ((x ^ 2 + y ^ 2) / 2)) - ((x + y) / 2 + sqrt (x * y)) =
            (4 * x * y + sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y) - (x + y) ^ 2 - 2 * (x + y) * sqrt (x * y)) / (2 * (x + y)) := by
      have h3 : sqrt ((x ^ 2 + y ^ 2) / 2) = Real.sqrt (2 * (x ^ 2 + y ^ 2)) / 2 := by
        have h4 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) = Real.sqrt (2 * (x ^ 2 + y ^ 2)) / 2 := by
          have h5 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) = Real.sqrt ((2 * (x ^ 2 + y ^ 2) ) / 4) := by ring_nf
          rw [h5]
          have h6 : Real.sqrt ((2 * (x ^ 2 + y ^ 2) ) / 4) = Real.sqrt (2 * (x ^ 2 + y ^ 2)) / 2 := by
            have h7 : Real.sqrt ((2 * (x ^ 2 + y ^ 2) ) / 4) = Real.sqrt (2 * (x ^ 2 + y ^ 2)) / Real.sqrt (4 : ℝ) := by 
              rw [← Real.sqrt_div (by nlinarith)]
            rw [h7]
            have h8 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
              rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
            rw [h8]
          exact h6
        exact h4
      rw [h3]
      have h3' : sqrt (x * y) = Real.sqrt (4 * (x * y) ) / 2 := by
        have h4 : Real.sqrt (x * y) = Real.sqrt (4 * (x * y) ) / 2 := by
          have h5 : Real.sqrt (x * y) = Real.sqrt ((4 * (x * y) ) / 4) := by ring_nf
          rw [h5]
          have h6 : Real.sqrt ((4 * (x * y) ) / 4) = Real.sqrt (4 * (x * y) ) / 2 := by
            have h7 : Real.sqrt ((4 * (x * y) ) / 4) = Real.sqrt (4 * (x * y) ) / Real.sqrt (4 : ℝ) := by 
              rw [← Real.sqrt_div (by nlinarith)]
            rw [h7]
            have h8 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
              rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
            rw [h8]
          exact h6
        exact h4
      rw [h3']
      field_simp
      nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sqrt_nonneg (4 * (x * y)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (x ^ 2 + y ^ 2) by nlinarith [sq_nonneg (x), sq_nonneg (y)]), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (x * y) by nlinarith [mul_pos hx hy])
      ]
    rw [h9] at *
    have h10 : (4 * x * y + sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y) - (x + y) ^ 2 - 2 * (x + y) * sqrt (x * y)) ≥ 0 := by
      have h13 : (sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y)) ≥ ( (x + y) ^ 2 - 4 * x * y + 2 * (x + y) * sqrt (x * y) ) := by
        have h14 : (sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y)) ^ 2 ≥ ( (x + y) ^ 2 - 4 * x * y + 2 * (x + y) * sqrt (x * y) ) ^ 2 := by
          have h15 : (sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y)) ^ 2 = (2 * (x^2 + y^2)) * (x + y) ^ 2 := by
            calc
              (sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y)) ^ 2 = (sqrt (2 * (x^2 + y^2)) ^ 2) * (x + y) ^ 2 := by ring
              _ = (2 * (x^2 + y^2)) * (x + y) ^ 2 := by 
                rw [Real.sq_sqrt]
                positivity
          rw [h15]
          have h17 : (2 * (x ^ 2 + y ^ 2)) * (x + y) ^ 2 ≥ ( (x + y) ^ 2 - 4 * x * y + 2 * (x + y) * sqrt (x * y) ) ^ 2 := by
            have h18 : 0 ≤ (x + y) := by nlinarith
            have h19 : 0 ≤ sqrt (x * y) := by positivity
            have h20 : (sqrt (x * y)) ^ 2 = x * y := by
              rw [Real.sq_sqrt]
              nlinarith [mul_pos hx hy]
            nlinarith [ sq_nonneg ( (x + y) * (x - y) ), sq_nonneg ( (x - y) ), sq_nonneg ( (x + y) * (x - y) ), sq_nonneg ( (sqrt (x * y)) - (x * y / (sqrt (x * y))) ), sq_nonneg ( (x + y) - 2 * sqrt (x * y) ), sq_nonneg ( (x - y) ), sq_nonneg ( (sqrt (x * y) ) - (x + y) / 2 ), mul_nonneg (show (0 : ℝ) ≤ (x + y) by positivity) (show (0 : ℝ) ≤ (sqrt (x * y)) by positivity) ]
          nlinarith
        have h21 : sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y) ≥ 0 := by positivity
        have h22 : ( (x + y) ^ 2 - 4 * x * y + 2 * (x + y) * sqrt (x * y) ) ≥ 0 := by
          nlinarith [ sq_nonneg ( (x + y) * (x - y) ), sq_nonneg ( (x - y) ), sq_nonneg ( (sqrt (x * y)) ^ 2 ), Real.sqrt_nonneg (x * y), Real.sq_sqrt (show (0 : ℝ) ≤ x * y by nlinarith [mul_pos hx hy] ) ]
        nlinarith [ Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sqrt_nonneg (x * y), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (x ^ 2 + y ^ 2) by nlinarith [sq_nonneg (x), sq_nonneg (y)] ), Real.sq_sqrt (show (0 : ℝ) ≤ x * y by nlinarith [mul_pos hx hy] ) ]
      nlinarith [ Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sqrt_nonneg (x * y), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (x ^ 2 + y ^ 2) by nlinarith [sq_nonneg (x), sq_nonneg (y)] ), Real.sq_sqrt (show (0 : ℝ) ≤ x * y by nlinarith [mul_pos hx hy] ) ]
    have h24 : (4 * x * y + sqrt (2 * (x ^ 2 + y ^ 2)) * (x + y) - (x + y) ^ 2 - 2 * (x + y) * sqrt (x * y) ) / (2 * (x + y)) ≥ 0 := by
      apply div_nonneg
      · linarith
      · -- denominator is > 0
        positivity
    linarith
  linarith