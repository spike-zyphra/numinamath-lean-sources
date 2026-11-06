import Mathlib

open Real

theorem algebra_186986 : sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) = sqrt 2 := by

  have h1 : 0 ≤ (4 + Real.sqrt 7 : ℝ) := by
    positivity

  have h2 : 0 ≤ (4 - Real.sqrt 7 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]

  have h3 : (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ) ^ 2 = 2 := by
    have h4 : (sqrt (4 + sqrt 7) ) ^ 2 = 4 + sqrt 7 := by
      rw [Real.sq_sqrt]
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    have h5 : (sqrt (4 - sqrt 7) ) ^ 2 = 4 - sqrt 7 := by
      rw [Real.sq_sqrt]
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    have h6 : (sqrt (4 + sqrt 7) ) * (sqrt (4 - sqrt 7) ) = 3 := by
      have h7 : (sqrt (4 + sqrt 7) ) * (sqrt (4 - sqrt 7) ) = Real.sqrt ((4 + Real.sqrt 7) * (4 - Real.sqrt 7) ) := by
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
        )]
      have h8 : (4 + Real.sqrt 7) * (4 - Real.sqrt 7) = 9 := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      have h9 : Real.sqrt ((4 + Real.sqrt 7) * (4 - Real.sqrt 7) ) = (3 : ℝ) := by
        rw [h8]
        have h2 : Real.sqrt (9 : ℝ) = (3 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith [h2]
      rw [h7, h9]
    calc
      (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7)) ^ 2
        = (sqrt (4 + sqrt 7) )^2 + (sqrt (4 - sqrt 7) )^2 - 2 * ( (sqrt (4 + sqrt 7) ) * (sqrt (4 - sqrt 7) ) ) := by ring
      _ = (4 + sqrt 7) + (4 - sqrt 7) - 2 * (3) := by
        rw [h4, h5, h6]
      _ = (2 : ℝ) := by
        nlinarith

  have h4 : sqrt (4 + sqrt 7) ≥ sqrt (4 - sqrt 7) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]

  have h5 : sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ≥ 0 := by
    linarith [Real.sqrt_nonneg (4 + sqrt 7), Real.sqrt_nonneg (4 - sqrt 7), h4]

  have h8 : sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) = Real.sqrt (2 : ℝ) := by
    have h9 : (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ) ^ 2 = (2 : ℝ) := h3
    have h10 : 0 ≤ (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ) := h5
    have h11 : Real.sqrt ( (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ) ^ 2 ) = Real.sqrt (2 : ℝ) := by
      rw [h9]
    have h12 : Real.sqrt ( (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ) ^ 2 ) = (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ) := by
      rw [Real.sqrt_sq (show 0 ≤ (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ) by linarith [h10] ) ]
    linarith [h11, h12, h5, Real.sqrt_nonneg (2 : ℝ) ]

  exact h8