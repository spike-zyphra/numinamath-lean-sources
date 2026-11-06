import Mathlib

open Real Set

theorem algebra_13272 :
    IsLeast {x | ∃ t : ℝ, x = sqrt (t ^ 2 - 6 * t + 25) + sqrt (t ^ 2 + 8 * t + 25)} (7 * sqrt 2) := by
  constructor
  · -- Show 7 * sqrt 2 is in the set
    use -1
    have h1 : sqrt ((-1 : ℝ) ^ 2 - 6 * (-1) + 25) = Real.sqrt 32 := by
      norm_num
    have h2 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h3 : sqrt ((-1 : ℝ) ^ 2 + 8 * (-1) + 25) = Real.sqrt 18 := by
      norm_num
    have h4 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h1, h3]
    rw [h2, h4]
    all_goals ring
  · -- Show that 7 * sqrt 2 is minimal
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt (t ^ 2 - 6 * t + 25) = Real.sqrt ((t - 3) ^ 2 + 16) := by
      ring_nf
    have h2 : sqrt (t ^ 2 + 8 * t + 25) = Real.sqrt ((t + 4) ^ 2 + 9) := by
      ring_nf
    rw [h1, h2] at ht
    have h3 : Real.sqrt ((t - 3) ^ 2 + 16) + Real.sqrt ((t + 4) ^ 2 + 9) ≥ 7 * Real.sqrt 2 := by
      have h4 : Real.sqrt ((t - 3) ^ 2 + 16) ≥ 0 := Real.sqrt_nonneg ((t - 3) ^ 2 + 16)
      have h5 : Real.sqrt ((t + 4) ^ 2 + 9) ≥ 0 := Real.sqrt_nonneg ((t + 4) ^ 2 + 9)
      have h6 : (Real.sqrt ((t - 3) ^ 2 + 16) + Real.sqrt ((t + 4) ^ 2 + 9)) ^ 2 ≥ (7 * Real.sqrt 2) ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt ((t - 3) ^ 2 + 16) - Real.sqrt ((t + 4) ^ 2 + 9)), 
                  sq_nonneg (t + 1), 
                  Real.sqrt_nonneg ((t - 3) ^ 2 + 16), 
                  Real.sqrt_nonneg ((t + 4) ^ 2 + 9), 
                  mul_nonneg (Real.sqrt_nonneg ((t - 3) ^ 2 + 16)) (Real.sqrt_nonneg ((t + 4) ^ 2 + 9)), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (t - 3) ^ 2 + 16 by nlinarith), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (t + 4) ^ 2 + 9 by nlinarith), 
                  Real.sqrt_nonneg 2, 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
                  sq_nonneg ((t + 1) * (Real.sqrt ((t - 3) ^ 2 + 16) + Real.sqrt ((t + 4) ^ 2 + 9)))
                ]
      have h7 : (7 * Real.sqrt 2) ^ 2 ≤ (Real.sqrt ((t - 3) ^ 2 + 16) + Real.sqrt ((t + 4) ^ 2 + 9)) ^ 2 := by 
        nlinarith [ h6 ]
      nlinarith [ Real.sqrt_nonneg ((t - 3) ^ 2 + 16), 
            Real.sqrt_nonneg ((t + 4) ^ 2 + 9), 
            Real.sqrt_nonneg 2, 
            h7, 
            Real.sqrt_nonneg 2
          ]
    have h4 : x = Real.sqrt ((t - 3) ^ 2 + 16) + Real.sqrt ((t + 4) ^ 2 + 9) := by
      linarith [ ht ]
    linarith [ h4, h3 ]