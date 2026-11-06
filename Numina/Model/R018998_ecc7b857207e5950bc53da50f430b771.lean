import Mathlib

theorem algebra_188041 (x : ℝ) :
    x^3 + x^2 + x = -1/3 ↔ x = -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3)) := by
  constructor
  · -- Assume x^3 + x^2 + x = -1/3, prove x = -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3))
    intro h_eq
    have h_eq1 : x^3 + x^2 + x + 1/3 = 0 := by linarith
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
    have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h6 : x = -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3)) := by
      have h7 : ( (x + (1 / 3) ) ^ 3 + (2 / 3) * (x + (1 / 3)) + 2 / 27 ) = 0 := by
        nlinarith [h_eq1]
      have h4 : ∀ (y : ℝ), ( (y + (1 / 3) ) ^ 3 + (2 / 3) * (y + (1 / 3)) + 2 / 27 ) = 0 → y = x := by
        intro y hy
        have hy1 : ( (y + (1 / 3) ) ^ 3 + (2 / 3) * (y + (1 / 3)) + 2 / 27 ) =0 := by linarith [hy]
        have h8 : (x + (1 / 3)) ^ 3 + (2 / 3) * (x + (1 / 3)) + 2 / 27 = (y + (1 / 3) ) ^ 3 + (2 / 3) * (y + (1 / 3)) + 2 / 27 := by linarith [h7, hy1]
        have h9 : x + (1 / 3) = y + (1 / 3) := by
          nlinarith [sq_nonneg ( (x + (1/3)) - (y + (1/3)) ), sq_nonneg ( (x + (1/3) ) + (y + (1/3) ) ), sq_nonneg ( (x + (1/3)) ), sq_nonneg ( (y + (1/3) ) ), h8, sq_nonneg ((x + (1/3) ) * (y + (1/3)) ) ]
        linarith [h9]
      have h8 : ( -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3) ) + (1 / 3) ) ^ 3 + (2 / 3) * ( -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3) ) + (1 / 3) ) + 2 / 27 = 0 := by
        have h3' : ( (2 : ℝ) ^ ((1 : ℝ)/3) ) ^3 = (2 : ℝ) := h3
        field_simp [(show 1 + (2 : ℝ) ^ ((1 : ℝ)/3) ≠ 0 by positivity)]
        nlinarith [ h3, sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1) ]
      have hx_eq : -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3) ) = x := by
        apply h4 ( -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3) ) )
        linarith [h8]
      linarith [hx_eq]
    linarith [h6]
  · -- Assume x = -1/(1 + (2 : ℝ) ^ ((1 : ℝ)/3)), prove x^3 + x^2 + x = -1/3
    intro h_eq
    rw [h_eq]
    have h3 : ( (2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (2 : ℝ) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    field_simp [(show 1 + (2 : ℝ) ^ ((1 : ℝ) / 3) ≠ 0 by positivity)]
    <;> nlinarith [ sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1), Real.rpow_pos_of_pos (show (2 : ℝ) > 0 by norm_num) (1 / 3), h3, sq_nonneg ( ( (2 : ℝ) ^ ((1 : ℝ)/3) + 1 ) ^ 2 ), mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) by positivity) (show (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) by positivity) ]