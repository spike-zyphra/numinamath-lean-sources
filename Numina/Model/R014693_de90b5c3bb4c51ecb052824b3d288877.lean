import Mathlib

theorem algebra_291359 {x y : ℝ} (h : (x + y) / (1 - x * y) = Real.sqrt 5) :
    (|1 - x * y| / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2))) = Real.sqrt 6 / 6 := by 
  have h1 : 1 - x * y ≠ 0 := by 
    by_contra h2 
    have : (x + y) / (1 - x * y) = 0 := by 
      rw [h2]
      norm_num 
    rw [this] at h
    have h3 : Real.sqrt 5 = (0 : ℝ) := by linarith 
    have h4 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
    linarith 
  have h2 : x + y = Real.sqrt 5 * (1 - x * y) := by 
    have h3 : (x + y) / (1 - x * y) = Real.sqrt 5 := h 
    have h4 : (x + y) = Real.sqrt 5 * (1 - x * y) := by
      field_simp [h1] at h3 ⊢
      <;> linarith 
    linarith 
  have h3 : (x + y) ^ 2 = 5 * (1 - x * y) ^ 2 := by
    calc
      (x + y) ^ 2 = (Real.sqrt 5 * (1 - x * y)) ^ 2 := by 
        rw [h2]
      _ = (Real.sqrt 5) ^ 2 * (1 - x * y) ^ 2 := by 
        ring_nf 
      _ = 5 * (1 - x * y) ^ 2 := by 
        rw [Real.sq_sqrt (by norm_num)]
        all_goals norm_num 
  have h4 : (1 + x ^ 2) * (1 + y ^ 2) = 6 * (1 - x * y) ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - (1 / 2)), sq_nonneg (x + y - Real.sqrt 5 * (1 - x * y)), h2, sq_nonneg (1 - x * y), Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (5 : ℝ)), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (6 : ℝ))]
  -- Compute sqrt(1 + x^2) * sqrt(1 + y^2) using sqrt(a) * sqrt(b) = sqrt(a * b)
  have h5 : Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) = Real.sqrt 6 * |1 - x * y| := by
    have h6 : Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) = Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) := by
      rw [← Real.sqrt_mul (by positivity)]
      <;> positivity
    rw [h6]
    rw [h4]
    have h7 : Real.sqrt (6 * (1 - x * y) ^ 2) = Real.sqrt 6 * Real.sqrt ((1 - x * y) ^ 2) := by
      rw [← Real.sqrt_mul (by positivity)]
      <;> positivity
    rw [h7]
    have h8 : Real.sqrt ((1 - x * y) ^ 2) = |1 - x * y| := by 
      rw [Real.sqrt_sq_eq_abs]
    rw [h8]
    <;> ring_nf <;> norm_num
    <;> positivity
  have h6 : |1 - x * y| / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)) = Real.sqrt 6 / 6 := by
    rw [h5]
    have h7 : |1 - x * y| > 0 := by
      apply abs_pos.mpr 
      exact h1
    field_simp [h7, Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num)]
    <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num)]
    <;> ring_nf <;> norm_num
  exact h6