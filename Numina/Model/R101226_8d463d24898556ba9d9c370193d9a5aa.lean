import Mathlib

theorem algebra_186984 (x : ℝ) (hx : 0 ≤ x) (h : Real.sqrt (2 * x + 5) + Real.sqrt (5 * x + 6) = Real.sqrt (12 * x + 25)) :
    x = 2 := by
  have h1 : Real.sqrt (2 * x + 5) ≥ 0 := Real.sqrt_nonneg (2 * x + 5)
  have h2 : Real.sqrt (5 * x + 6) ≥ 0 := Real.sqrt_nonneg (5 * x + 6)
  have h3 : Real.sqrt (12 * x + 25) ≥ 0 := Real.sqrt_nonneg (12 * x + 25)
  have eq1 : (Real.sqrt (2 * x + 5) + Real.sqrt (5 * x + 6)) ^ 2 = (Real.sqrt (12 * x + 25)) ^ 2 := by
    rw [h]
  have eq2 : (Real.sqrt (2 * x + 5) + Real.sqrt (5 * x + 6)) ^ 2 = (Real.sqrt (2 * x + 5)) ^ 2 + (Real.sqrt (5 * x + 6)) ^ 2 + 2 * (Real.sqrt (2 * x + 5) * Real.sqrt (5 * x + 6)) := by ring
  have eq3 : (Real.sqrt (12 * x + 25)) ^ 2 = 12 * x + 25 := by
    apply Real.sq_sqrt
    linarith
  rw [eq2] at eq1
  rw [eq3] at eq1
  have eq4 : (Real.sqrt (2 * x + 5)) ^ 2 = 2 * x + 5 := by
    apply Real.sq_sqrt
    linarith
  have eq5 : (Real.sqrt (5 * x + 6)) ^ 2 = 5 * x + 6 := by
    apply Real.sq_sqrt
    linarith
  rw [eq4, eq5] at eq1
  have eq6 : 2 * (Real.sqrt (2 * x + 5) * Real.sqrt (5 * x + 6)) = 5 * x + 14 := by
    nlinarith [eq1]
  have eq7 : Real.sqrt (2 * x + 5) * Real.sqrt (5 * x + 6) = Real.sqrt ((2 * x + 5) * (5 * x + 6)) := by
    rw [← Real.sqrt_mul (by linarith)]
  have eq8 : (2 * Real.sqrt ((2 * x + 5) * (5 * x + 6))) ^ 2 = (5 * x + 14) ^ 2 := by
    have eq7' : Real.sqrt (2 * x + 5) * Real.sqrt (5 * x + 6) = Real.sqrt ((2 * x + 5) * (5 * x + 6)) := by
      rw [← Real.sqrt_mul (by linarith)]
    nlinarith [eq6, eq7']
  have eq9 : (2 * Real.sqrt ((2 * x + 5) * (5 * x + 6))) ^ 2 = 4 * ((2 * x + 5) * (5 * x + 6)) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x + 5) * (5 * x + 6) by nlinarith)]
  have eq10 : 4 * ((2 * x + 5) * (5 * x + 6)) = (5 * x + 14) ^ 2 := by
    nlinarith [eq8, eq9]
  have h4 : (x - 2) * (15 * x + 38) = 0 := by
    nlinarith [eq10]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- x - 2 = 0
    linarith
  · -- 15 * x + 38 = 0
    nlinarith