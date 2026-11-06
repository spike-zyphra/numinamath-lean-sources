import Mathlib

open Real

theorem algebra_298963 {a : ℝ} (ha : a ≥ 5 / 2) :
    sqrt (a + 2 + 3 * sqrt (2 * a - 5)) - sqrt (a - 2 + sqrt (2 * a - 5)) = sqrt 2 := by

  have ha1 : 2 * a - 5 ≥ 0 := by
    nlinarith

  have h1 : sqrt (a + 2 + 3 * sqrt (2 * a - 5)) = (sqrt (2 * a - 5) + 3) / Real.sqrt 2 := by
    have h2 : (a + 2 + 3 * sqrt (2 * a - 5)) = ((sqrt (2 * a - 5) + 3) / Real.sqrt 2) ^ 2 := by
      have h3 : ((sqrt (2 * a - 5) + 3) / Real.sqrt 2) ^ 2 = ((sqrt (2 * a - 5) + 3) )^2 / (Real.sqrt 2 ^ 2) := by
        field_simp
      have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h5 : ((sqrt (2 * a - 5) + 3)) ^ 2 = 2 * (a + 2 + 3 * sqrt (2 * a - 5)) := by
        have h6 : (sqrt (2 * a - 5)) ^ 2 = 2 * a - 5 := by
          rw [Real.sq_sqrt]
          nlinarith
        nlinarith [h6]
      rw [h3, h4]
      field_simp at *
      nlinarith [h5, Real.sqrt_nonneg 2, ha1]
    rw [h2]
    have h7 : 0 ≤ (sqrt (2 * a - 5) : ℝ) := Real.sqrt_nonneg (2 * a - 5)
    have h8 : 0 ≤ ((sqrt (2 * a - 5) + 3) / Real.sqrt 2 : ℝ) := by
      have h9 : 0 ≤ Real.sqrt (2 * a - 5) := Real.sqrt_nonneg (2 * a - 5)
      have h10 : 0 < Real.sqrt (2 : ℝ) := by
        positivity
      have h11 : 0 ≤ sqrt (2 * a - 5) + 3 := by
        linarith [h9]
      have h12 : 0 ≤ (sqrt (2 * a - 5) + 3) / Real.sqrt (2 : ℝ) := by
        apply div_nonneg
        linarith
        positivity
      linarith
    rw [Real.sqrt_sq (by linarith [h8])]

  have h2 : sqrt (a - 2 + sqrt (2 * a - 5)) = (sqrt (2 * a - 5) + 1) / Real.sqrt 2 := by
    have h2 : (a - 2 + sqrt (2 * a - 5)) = ((sqrt (2 * a - 5) + 1) / Real.sqrt 2) ^ 2 := by
      have h3 : ((sqrt (2 * a - 5) + 1) / Real.sqrt 2) ^ 2 = ((sqrt (2 * a - 5) + 1) )^2 / (Real.sqrt 2 ^ 2) := by
        field_simp
      have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h5 : ((sqrt (2 * a - 5) + 1)) ^ 2 = 2 * (a - 2 + sqrt (2 * a - 5)) := by
        have h6 : (sqrt (2 * a - 5)) ^ 2 = 2 * a - 5 := by
          rw [Real.sq_sqrt]
          nlinarith
        nlinarith [h6]
      rw [h3, h4]
      field_simp at *
      nlinarith [h5, Real.sqrt_nonneg 2, ha1]
    rw [h2]
    have h7 : 0 ≤ (sqrt (2 * a - 5) : ℝ) := Real.sqrt_nonneg (2 * a - 5)
    have h8 : 0 ≤ ((sqrt (2 * a - 5) + 1) / Real.sqrt 2 : ℝ) := by
      have h9 : 0 ≤ Real.sqrt (2 * a - 5) := Real.sqrt_nonneg (2 * a - 5)
      have h10 : 0 < Real.sqrt (2 : ℝ) := by
        positivity
      have h11 : 0 ≤ sqrt (2 * a - 5) + 1 := by
        linarith [h9]
      have h12 : 0 ≤ (sqrt (2 * a - 5) + 1) / Real.sqrt (2 : ℝ) := by
        apply div_nonneg
        linarith
        positivity
      linarith
    rw [Real.sqrt_sq (by linarith [h8])]

  rw [h1, h2]
  have h7 : 0 < Real.sqrt 2 := by
    positivity

  field_simp at *
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (2 * a - 5), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * a - 5 by linarith)]