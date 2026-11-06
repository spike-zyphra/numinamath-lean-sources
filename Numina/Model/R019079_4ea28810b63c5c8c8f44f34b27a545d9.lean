import Mathlib

theorem algebra_192535 (x : ℝ) (hx : x ≥ 4) (h : (3 * x - 1) * Real.sqrt (x - 4) = 17 * Real.sqrt 2) :
    x = 6 := by
  have h1 : Real.sqrt (x - 4) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : Real.sqrt (2) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h3 : (3 * x - 1) ^ 2 * (x - 4) = 578 := by
    have eq1 : (Real.sqrt (x - 4)) ^ 2 = x - 4 := by
      rw [Real.sq_sqrt]
      linarith
    have eq2 : (Real.sqrt (2)) ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have eq3 : ((3 * x - 1) * Real.sqrt (x - 4)) ^ 2 = (17 * Real.sqrt 2) ^ 2 := by
      rw [h]
    have eq4 : ((3 * x - 1) * Real.sqrt (x - 4)) ^ 2 = (3 * x - 1) ^ 2 * (Real.sqrt (x - 4) ^ 2) := by
      ring
    have eq5 : (17 * Real.sqrt 2) ^ 2 = 578 := by
      calc
        (17 * Real.sqrt 2) ^ 2 = (17 : ℝ) ^ 2 * (Real.sqrt 2) ^ 2 := by ring
        _ = (17 : ℝ) ^ 2 * (2 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals linarith
        _ = (289 : ℝ) * (2 : ℝ) := by norm_num
        _ = (578 : ℝ) := by norm_num
    nlinarith [eq3, eq4, eq5, eq1, sq_nonneg (Real.sqrt (x - 4)), sq_nonneg (Real.sqrt 2)]
  have h4 : (x - 6) * (9 * x^2 + 12 * x + 97) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- When $x - 6 = 0$, then $x = 6$
    linarith
  · -- We have to show that $9 * x^2 + 12 * x + 97 = 0$ has no real solution
    have h7 : (9 * x ^ 2 + 12 * x + 97) > (0 : ℝ) := by
      nlinarith [sq_nonneg (x + 6 / 9), sq_nonneg (x - 6), Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 4) by linarith)]
    have h8 : (9 * x^2 + 12 * x + 97) ≠ 0 := by
      nlinarith
    have : (9 * x ^ 2 + 12 * x + 97) = 0 := by linarith [h6]
    contradiction