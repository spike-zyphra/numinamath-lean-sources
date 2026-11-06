import Mathlib

open Real

theorem algebra_320406 {m : ℝ} (hm : m > 1) (a b : ℝ)
    (ha : a = sqrt (m + 1) - sqrt m) (hb : b = sqrt m - sqrt (m - 1)) :
    a < b := by
  rw [ha, hb]
  have h4 : sqrt (m + 1) + sqrt (m - 1) < 2 * sqrt m := by
    have h5 : sqrt (m + 1) + sqrt (m - 1) > 0 := by positivity
    have h6 : sqrt m > 0 := by positivity
    have h7 : (sqrt (m + 1) + sqrt (m - 1)) ^ 2 < (2 * sqrt m) ^ 2 := by
      have h8 : (sqrt (m + 1) + sqrt (m - 1)) ^ 2 = (sqrt (m + 1)) ^ 2 + (sqrt (m - 1)) ^ 2 + 2 * (sqrt (m + 1) * sqrt (m - 1)) := by ring
      have h9 : (sqrt (m + 1)) ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
      have h10 : (sqrt (m - 1)) ^ 2 = m - 1 := Real.sq_sqrt (by linarith)
      have h11 : sqrt (m + 1) * sqrt (m - 1) = sqrt ((m + 1) * (m - 1)) := by
        rw [← Real.sqrt_mul (by linarith)]
      rw [h8, h9, h10, h11]
      have h12 : (2 * sqrt m) ^ 2 = 4 * (sqrt m) ^ 2 := by ring
      rw [h12]
      have h13 : (m + 1) * (m - 1) = m ^ 2 - 1 := by ring
      rw [h13]
      have h14 : sqrt ((m : ℝ) ^ 2 - 1) < m := by
        have h15 : sqrt ((m : ℝ) ^ 2 - 1) < sqrt ((m : ℝ) ^ 2) := by
          apply Real.sqrt_lt_sqrt
          all_goals nlinarith
        have h16 : sqrt ((m : ℝ) ^ 2) = m := by
          rw [Real.sqrt_sq]
          all_goals nlinarith
        linarith
      have h17 : (sqrt (m ^ 2 - 1)) ^ 2 = m ^ 2 - 1 := by
        rw [Real.sq_sqrt]
        all_goals nlinarith
      have h18 : (sqrt m) ^ 2 = m := by
        rw [Real.sq_sqrt]
        all_goals nlinarith
      nlinarith [Real.sqrt_nonneg ((m : ℝ) ^ 2 - 1), Real.sqrt_nonneg m]
    have h19 : sqrt ((sqrt (m + 1) + sqrt (m - 1)) ^ 2) < sqrt ((2 * sqrt m) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    have h20 : sqrt ((sqrt (m + 1) + sqrt (m - 1)) ^ 2) = sqrt (m + 1) + sqrt (m - 1) := by
      rw [Real.sqrt_sq]
      all_goals positivity
    have h21 : sqrt ((2 * sqrt m) ^ 2) = 2 * sqrt m := by
      rw [Real.sqrt_sq]
      all_goals positivity
    linarith
  have h5 : sqrt (m + 1) - sqrt m < sqrt m - sqrt (m - 1) := by
    linarith [h4]
  linarith