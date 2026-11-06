import Mathlib

theorem number_theory_72100 : ∃ m n : ℤ, (m / n : ℝ) = (Real.sqrt 50 + 7) ^ ((1 : ℝ) / 3) - (Real.sqrt 50 - 7) ^ ((1 : ℝ) / 3) := by
  use 2
  use 1
  have h2 : ( (Real.sqrt 50 + 7) : ℝ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7) : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
    -- define the cube root of Real.sqrt 50 + 7
    -- define the cube root of Real.sqrt 50 - 7
    have ha3 : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 = Real.sqrt 50 + 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 50, Real.sq_sqrt (show (0 : ℝ) ≤ (50 : ℝ) by norm_num) ]
    -- computation of ( Real.sqrt 50 - 7 )^ (1/3) * ( Real.sqrt 50 + 7 )^ (1/3) = ( Real.sqrt 50 - 7 ) * ( Real.sqrt 50 + 7 )^ (1/3) )
    have hb3 : ( ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 = Real.sqrt 50 - 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 50, Real.sq_sqrt (show (0 : ℝ) ≤ (50 : ℝ) by norm_num) ]
    have h7 : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) * ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) = (1 : ℝ) := by
      have h8 : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) * ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) = ( (Real.sqrt 50 + 7 : ℝ) * (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.mul_rpow]
        all_goals
          nlinarith [Real.sqrt_nonneg 50, Real.sq_sqrt (show (0 : ℝ) ≤ (50 : ℝ) by norm_num) ]
      rw [h8]
      have h9 : ( (Real.sqrt 50 + 7 : ℝ) * (Real.sqrt 50 - 7 : ℝ) ) = (1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 50, Real.sq_sqrt (show (0 : ℝ) ≤ (50 : ℝ) by norm_num) ]
      rw [h9]
      norm_num
    have hx3 : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 = 14 - 3 * ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) := by
      have h8 : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 = ( ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 - ( ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 ) - 3 * ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) * ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) * ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) := by
        ring_nf
      rw [h8, ha3, hb3, h7]
      all_goals nlinarith
    have hx : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) = 2 := by
      have h11 : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 + 3 * ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) - 14 = 0 := by
        nlinarith [hx3]
      have h12 : ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 3 + 3 * ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) - 14 = (( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) - 2) * (( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) ^ 2 + 2 * ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) ) + 7 ) := by
        ring_nf
      rw [h12] at h11
      cases' (mul_eq_zero.1 h11) with h13 h14
      · -- When (x - 2) = 0, x = 2
        linarith
      · -- When (x^2 + 2x + 7) = 0, no real solution, as discriminant is < 0
        nlinarith [sq_nonneg ( ( (Real.sqrt 50 + 7 : ℝ) ) ^ ((1 : ℝ) / 3) - ( (Real.sqrt 50 - 7 : ℝ) ) ^ ((1 : ℝ) / 3) + 1 ) ]
    linarith
  norm_num at h2 ⊢
  linarith