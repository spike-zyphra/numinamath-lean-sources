import Mathlib

theorem algebra_8224 (m n : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (h : (n + Real.sqrt (m^2 + 4)) * (m + Real.sqrt (n^2 + 4)) = 4) :
    m^2009 + n^2009 = 0 := by
  have h1 : 0 ≤ Real.sqrt (m^2 + 4) := Real.sqrt_nonneg (m^2 + 4)
  have h2 : 0 ≤ Real.sqrt (n^2 + 4) := Real.sqrt_nonneg (n^2 + 4)
  have h3 : Real.sqrt (m^2 + 4) ≥ m := by
    nlinarith [Real.sqrt_nonneg (m^2 + 4), Real.sq_sqrt (show 0 ≤ (m^2 + 4) by nlinarith)]
  have h4 : Real.sqrt (n^2 + 4) ≥ n := by
    nlinarith [Real.sqrt_nonneg (n^2 + 4), Real.sq_sqrt (show 0 ≤ (n^2 + 4) by nlinarith)]
  have h5 : Real.sqrt (m^2 + 4) > m := by
    have h6 : 0 < (4 : ℝ) := by norm_num
    have h7 : m^2 < m^2 + 4 := by nlinarith
    have h8 : Real.sqrt (m^2) < Real.sqrt (m^2 + 4) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    have h9 : Real.sqrt (m^2) = m := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h9, h8, Real.sqrt_nonneg (m^2 + 4)]
  have h6 : Real.sqrt (n^2 + 4) > n := by
    have h7 : 0 < (4 : ℝ) := by norm_num
    have h8 : n^2 < n^2 + 4 := by nlinarith
    have h9 : Real.sqrt (n^2) < Real.sqrt (n^2 + 4) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    have h10 : Real.sqrt (n^2) = n := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h10, h9, Real.sqrt_nonneg (n^2 + 4)]
  have h7 : m = 0 := by
    nlinarith [sq_nonneg (m - n), sq_nonneg (Real.sqrt (m^2 + 4) - Real.sqrt (n^2 + 4)), 
      Real.sq_sqrt (show 0 ≤ (m^2 + 4 : ℝ) by nlinarith), 
      Real.sq_sqrt (show 0 ≤ (n^2 + 4 : ℝ) by nlinarith), 
      mul_nonneg hm hn
    ]
  have h8 : n = 0 := by
    nlinarith [sq_nonneg (m - n), sq_nonneg (Real.sqrt (m^2 + 4) - Real.sqrt (n^2 + 4)), 
      Real.sq_sqrt (show 0 ≤ (m^2 + 4 : ℝ) by nlinarith), 
      Real.sq_sqrt (show 0 ≤ (n^2 + 4 : ℝ) by nlinarith), 
      mul_nonneg hm hn
    ]
  rw [h7, h8]
  norm_num