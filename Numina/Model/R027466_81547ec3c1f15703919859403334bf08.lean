import Mathlib

theorem inequalities_305066 (p q r : ℝ) (hpqr : 0 ≤ p ∧ 0 ≤ q ∧ 0 ≤ r)
    (h : p^2 + q^2 + r^2 = 2) : p + q + r - p * q * r ≤ 2 := by
  have h1 : 0 ≤ p := hpqr.left
  have h2 : 0 ≤ q := hpqr.right.left
  have h3 : 0 ≤ r := hpqr.right.right
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p), 
      sq_nonneg (p + q + r - 2), 
      mul_nonneg (show (0 : ℝ) ≤ p by linarith) 
          (show (0 : ℝ) ≤ q by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ p by linarith) 
          (show (0 : ℝ) ≤ r by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ q by linarith) 
          (show (0 : ℝ) ≤ r by linarith), 
      sq_nonneg (p * q - r), 
      sq_nonneg (p - 1), sq_nonneg (q - 1), sq_nonneg (r - 1)
  ]