import Mathlib

theorem algebra_274462 : ∃ n : ℤ, (9 + 4 * √5) ^ ((1 : ℝ) / 3) + (9 - 4 * √5) ^ ((1 : ℝ) / 3) = n := by
  use 3
  have h1 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) ^ 3 = (9 + 4 * Real.sqrt 5) := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num 
    all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
  have h2 : ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) ^ 3 = (9 - 4 * Real.sqrt 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
  have h3 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h4 : ((9 + 4 * Real.sqrt 5) * (9 - 4 * Real.sqrt 5)) = 1 := by
    nlinarith [Real.sqrt_nonneg 5, h3]
  have h5 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) = 1 := by
    have h6 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) = ((9 + 4 * Real.sqrt 5) * (9 - 4 * Real.sqrt 5)) ^ ((1 : ℝ) / 3) := by 
      rw [← Real.mul_rpow]
      all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
    rw [h6, h4]
    all_goals norm_num
  have h7 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) = (3 : ℝ) := by
    have h71 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) ^ 3 = 18 + 3 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) := by
      have h8 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) ^ 3 =
        ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) ^ 3 + ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) := by ring
      have eq1 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) ^ 3 + ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) ^ 3 = (9 + 4 * Real.sqrt 5) + (9 - 4 * Real.sqrt 5) := by 
        rw [h1, h2]
      have eq2 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) = 1 := by
        linarith [h5]
      have eq3 : 3 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) = 3 * 1 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) := by
        calc
          3 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) 
            = 3 * (( (9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) * ( (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) )) * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) := by ring 
          _ = 3 * (1 : ℝ) * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) := by 
            rw [show (( (9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) * ( (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) )) = (1 : ℝ) by linarith [h5] ]
          _ = 3 * 1 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3)) := by ring
      nlinarith [eq1, eq2, eq3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 5]
    have h72 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) ^ 3 - 3 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) - 18 = 0 := by
      linarith [h71]
    have h73 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) - (3 : ℝ)) = 0 := by
      have h74 : ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) ^ 3 - 3 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) - 18 = ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) - 3) * (((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) ^ 2 + 3 * ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) ) + 6) := by 
        ring
      rw [h74] at h72
      cases' (mul_eq_zero.1 h72) with h75 h76
      · -- Case where \( y - 3 = 0 \)
        linarith 
      · -- Case where \( y^2 + 3 y + 6 = 0 \)
        nlinarith [sq_nonneg ((9 + 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (9 - 4 * Real.sqrt 5) ^ ((1 : ℝ) / 3) + (3 / 2 : ℝ))]
    linarith 
  exact_mod_cast h7