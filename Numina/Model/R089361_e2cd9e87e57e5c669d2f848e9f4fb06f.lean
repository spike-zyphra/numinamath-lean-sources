import Mathlib

theorem algebra_318819 {a b c : ℝ} (ha : a ≠ 0) (hA : a * Real.sqrt 3 + b = Real.sqrt 3 + 2)
    (hB : a * (-1) + b = Real.sqrt 3) (hC : a * c + b = 2 - c) :
    a - b + c = -2 := by 
  have eq_a : a = Real.sqrt 3 - 1 := by
    have h1 : a * (Real.sqrt 3 + 1) = 2 := by
      linarith [hA, hB, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
    have h2 : Real.sqrt 3 + 1 ≠ 0 := by
      positivity
    have h3 : a = 2 / (Real.sqrt 3 + 1) := by 
      field_simp [h2] at h1 ⊢
      <;> nlinarith
    have eq2 : 2 / (Real.sqrt 3 + 1) = Real.sqrt 3 - 1 := by
      field_simp [show Real.sqrt 3 + 1 ≠ 0 by positivity, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      <;> ring_nf <;> norm_num [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    linarith [eq2, h3, Real.sqrt_nonneg 3]
  have eq_b : b = 2 * Real.sqrt 3 - 1 := by
    rw [eq_a] at hB
    linarith [hB, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ))]
  -- From hC: a * c + b = 2 - c. Now substitute the values of a and b.
  have eq_c : c = Real.sqrt 3 - 2 := by
    rw [eq_a, eq_b] at hC
    -- Solve the equation
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), sq_nonneg (c + 2 - Real.sqrt 3), sq_nonneg (a - (Real.sqrt 3 - 1)), sq_nonneg (b - (2 * Real.sqrt 3 - 1)), Real.sqrt_nonneg 3]
  -- Finally compute a - b + c.
  rw [eq_a, eq_b, eq_c]
  -- Simplify and prove that it's equal to -2.
  nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]