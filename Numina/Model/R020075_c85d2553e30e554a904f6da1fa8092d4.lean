import Mathlib

theorem algebra_198926 :
    Real.sqrt (2 + 2 / 3 : ℝ) = 2 * Real.sqrt (2 / 3 : ℝ) ∧
    Real.sqrt (5 + 5 / 24 : ℝ) = 5 * Real.sqrt (5 / 24 : ℝ) := by
  constructor
  · -- Prove that $\sqrt{2 \frac{2}{3}}=2 \sqrt{\frac{2}{3}}$
    have h1 : Real.sqrt (2 + 2 / 3 : ℝ) = Real.sqrt (8 / 3 : ℝ) := by
      norm_num
    rw [h1] at *
    have h2 : Real.sqrt (8 / 3 : ℝ) ≥ 0 := by positivity
    have h3 : 2 * Real.sqrt (2 / 3 : ℝ) ≥ 0 := by positivity
    have h4 : (Real.sqrt (8 / 3 : ℝ)) ^ 2 = (2 * Real.sqrt (2 / 3 : ℝ)) ^ 2 := by
      have h5 : (Real.sqrt (8 / 3 : ℝ)) ^ 2 = 8 / 3 := Real.sq_sqrt (by norm_num)
      have h6 : (2 * Real.sqrt (2 / 3 : ℝ)) ^ 2 = 4 * (Real.sqrt (2 / 3 : ℝ)) ^ 2 := by ring
      have h7 : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
      rw [h5]
      rw [h6, h7]
      norm_num
    have h8 : Real.sqrt (8 / 3 : ℝ) = 2 * Real.sqrt (2 / 3 : ℝ) := by
      nlinarith [h4, h2, h3]
    linarith [h8]
  · -- Prove that $\sqrt{5 \frac{5}{24}}=5 \sqrt{\frac{5}{24}}$
    have h1 : Real.sqrt (5 + 5 / 24 : ℝ) = Real.sqrt (125 / 24 : ℝ) := by
      norm_num
    rw [h1] at *
    have h2 : Real.sqrt (125 / 24 : ℝ) ≥ 0 := by positivity
    have h3 : 5 * Real.sqrt (5 / 24 : ℝ) ≥ 0 := by positivity
    have h4 : (Real.sqrt (125 / 24 : ℝ)) ^ 2 = (5 * Real.sqrt (5 / 24 : ℝ)) ^ 2 := by
      have h5 : (Real.sqrt (125 / 24 : ℝ)) ^ 2 = 125 / 24 := Real.sq_sqrt (by norm_num)
      have h6 : (5 * Real.sqrt (5 / 24 : ℝ)) ^ 2 = 25 * (Real.sqrt (5 / 24 : ℝ)) ^ 2 := by ring
      have h7 : (Real.sqrt (5 / 24 : ℝ)) ^ 2 = 5 / 24 := Real.sq_sqrt (by norm_num)
      rw [h5]
      rw [h6, h7]
      norm_num
    have h8 : Real.sqrt (125 / 24 : ℝ) = 5 * Real.sqrt (5 / 24 : ℝ) := by
      nlinarith [h4, h2, h3]
    linarith [h8]