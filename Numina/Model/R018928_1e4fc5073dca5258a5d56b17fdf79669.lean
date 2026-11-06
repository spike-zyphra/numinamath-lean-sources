import Mathlib

theorem algebra_203339 : Real.sqrt (3 + Real.sqrt 5) + Real.sqrt (3 - Real.sqrt 5) = Real.sqrt 10 := by
  have h1 : Real.sqrt (3 + Real.sqrt 5) ≥ 0 := by positivity
  have h2 : Real.sqrt (3 - Real.sqrt 5) ≥ 0 := by positivity
  have h3 : (Real.sqrt (3 + Real.sqrt 5) + Real.sqrt (3 - Real.sqrt 5)) ^ 2 = 10 := by
    have h4 : (Real.sqrt (3 + Real.sqrt 5)) ^ 2 = 3 + Real.sqrt 5 := by
      exact Real.sq_sqrt (by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])
    have h5 : (Real.sqrt (3 - Real.sqrt 5)) ^ 2 = 3 - Real.sqrt 5 := by
      exact Real.sq_sqrt (by
        have h6 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
        have h7 : Real.sqrt 5 ≤ 3 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5, Real.sqrt_nonneg 5]
        nlinarith [h6, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      )
    have h8 : (Real.sqrt (3 + Real.sqrt 5)) ^ 2 + (Real.sqrt (3 - Real.sqrt 5)) ^ 2 = 6 := by
      rw [h4, h5]
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h9 : Real.sqrt (3 + Real.sqrt 5) * Real.sqrt (3 - Real.sqrt 5) = 2 := by
      have h10 : Real.sqrt (3 + Real.sqrt 5) * Real.sqrt (3 - Real.sqrt 5) = Real.sqrt ((3 + Real.sqrt 5) * (3 - Real.sqrt 5)) := by
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        )]
      have h11 : (3 + Real.sqrt 5) * (3 - Real.sqrt 5) = 4 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      rw [h10]
      rw [h11]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    calc
      (Real.sqrt (3 + Real.sqrt 5) + Real.sqrt (3 - Real.sqrt 5)) ^ 2
          = (Real.sqrt (3 + Real.sqrt 5)) ^ 2 + (Real.sqrt (3 - Real.sqrt 5)) ^ 2 + 2 * (Real.sqrt (3 + Real.sqrt 5) * Real.sqrt (3 - Real.sqrt 5)) := by ring
      _ = 6 + 2 * (Real.sqrt (3 + Real.sqrt 5) * Real.sqrt (3 - Real.sqrt 5)) := by nlinarith [h8]
      _ = 6 + 2 * (2) := by rw [h9]
      _ = 10 := by norm_num
  have h4 : Real.sqrt (3 + Real.sqrt 5) + Real.sqrt (3 - Real.sqrt 5) ≥ 0 := by positivity
  have h5 : Real.sqrt 10 ≥ 0 := by positivity
  have h6 : (Real.sqrt (3 + Real.sqrt 5) + Real.sqrt (3 - Real.sqrt 5)) ^ 2 = (Real.sqrt 10) ^ 2 := by
    rw [h3]
    rw [Real.sq_sqrt (by norm_num)]
  have h7 : Real.sqrt (3 + Real.sqrt 5) + Real.sqrt (3 - Real.sqrt 5) = Real.sqrt 10 := by nlinarith [Real.sqrt_nonneg 10, h4]
  exact h7