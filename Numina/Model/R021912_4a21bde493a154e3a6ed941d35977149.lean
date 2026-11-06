import Mathlib

theorem algebra_325035 {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : 2 * p + Real.sqrt (p * q) - q + Real.sqrt p + Real.sqrt q = 0) :
    (2 * Real.sqrt p - Real.sqrt q + 2)^3 = 1 := by
  have h1 : 0 ≤ p := by linarith
  have h2 : 0 ≤ q := by linarith
  have h3 : Real.sqrt (p * q) = Real.sqrt p * Real.sqrt q := by
    rw [Real.sqrt_mul (by nlinarith)]
  rw [h3] at h
  have h4 : Real.sqrt p ≥ 0 := by positivity
  have h5 : Real.sqrt q ≥ 0 := by positivity
  have h6 : Real.sqrt q = 2 * Real.sqrt p + 1 := by
    nlinarith [sq_nonneg (Real.sqrt p - 1), sq_nonneg (Real.sqrt q - (2 * Real.sqrt p + 1)), 
              Real.sq_sqrt (show (0 : ℝ) ≤ p by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ q by linarith),
              mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg q)]
  have h7 : 2 * Real.sqrt p - Real.sqrt q + 2 = 1 := by
    rw [h6]
    nlinarith [Real.sqrt_nonneg p]
  rw [h7]
  norm_num