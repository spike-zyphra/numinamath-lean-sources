import Mathlib

theorem algebra_325656 (a b : ℝ) (ha : a = 20 + 14 * Real.sqrt 2) (hb : b = 20 - 14 * Real.sqrt 2) :
    (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3)) = 4 := by
  have ha1 : a = 20 + 14 * Real.sqrt 2 := ha
  have hb1 : b = 20 - 14 * Real.sqrt 2 := hb
  have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (show (2 : ℝ) > 0 by norm_num)
  have ha2 : a > 0 := by 
    rw [ha1]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have hb2 : b > 0 := by
    rw [hb1]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 1)]
  have h2 : a * b = 8 := by
    rw [ha1, hb1]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h3 : (a ^ ((1 : ℝ) / 3) ) ^ 3 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h4 : (b ^ ((1 : ℝ) / 3) ) ^ 3 = b := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h3' : (a ^ ((1 : ℝ) / 3) ) * (b ^ ((1 : ℝ) / 3) ) = (a * b) ^ ((1 : ℝ) / 3) := by 
    rw [← Real.mul_rpow]
    all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), ha2, hb2]
  have hx3_eq : (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3)) ^ 3 = 40 + 6 * (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) := by
    calc
      (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) ^ 3 = ( (a ^ ((1 : ℝ) / 3) ) ^ 3 + (b ^ ((1 : ℝ) / 3) ) ^ 3 ) + 3 * ( (a ^ ((1 : ℝ) / 3) ) * (b ^ ((1 : ℝ) / 3) ) ) * (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) := by
        ring
      _ = ( a + b ) + 3 * ( (a * b) ^ ((1 : ℝ) / 3) ) * (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) := by
        rw [h3, h4, h3']
      _ = ( 40 ) + 3 * ( 2 ) * (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) := by
        have h5 : (a * b) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
          rw [show a * b = (8 : ℝ) by linarith [h2]]
          have h8 : ((8 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
            have h10 : ((8 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
              rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
              rw [← Real.rpow_mul]
              norm_num
              all_goals norm_num
            linarith [h10]
          linarith [h8]
        rw [h5]
        have h6 : a + b = 40 := by
          rw [ha1, hb1]
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [h6]
      _ = (40 + 6 * (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) )) := by nlinarith
  have eq1 : (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) ^ 3 - 6 * (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) - 40 = 0 := by
    linarith [hx3_eq]
  have eq2 : (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) - 4) * ((a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) )^2 + 4 * (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) + 10) = 0 := by
    nlinarith [eq1]
  cases (mul_eq_zero.mp eq2) with
  | inl h => 
    linarith
  | inr h => 
    nlinarith [sq_nonneg ( (a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) ) + 2 ), sq_nonneg ( (a ^ ((1 : ℝ) / 3) - b ^ ((1 : ℝ) / 3) ) ) ]