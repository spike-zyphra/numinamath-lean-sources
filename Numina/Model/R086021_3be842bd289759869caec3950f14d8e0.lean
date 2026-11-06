import Mathlib

theorem algebra_302040 {x y : ℝ} (h : x + Real.sqrt (x ^ 2 + 1) = 1 / (y + Real.sqrt (y ^ 2 + 1))) :
    x + y = 0 := by 
  have h1 : y + Real.sqrt (y ^ 2 + 1) ≠ 0 := by
    by_contra h2
    have h3 : 1 / (y + Real.sqrt (y ^ 2 + 1)) = 0 := by
      field_simp [h2]
    rw [h3] at h
    have h4 : x + Real.sqrt (x ^ 2 + 1) = 0 := by linarith
    have h5 : Real.sqrt (x ^ 2 + 1) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 1)
    have h6 : Real.sqrt (x ^ 2 + 1) = -x := by linarith [h4, h5]
    have h7 : 0 ≤ Real.sqrt (x ^ 2 + 1) := Real.sqrt_nonneg (x ^ 2 + 1)
    have h8 : -x ≥ 0 := by nlinarith [h4, Real.sqrt_nonneg (x ^ 2 + 1)]
    have h9 : Real.sqrt (x ^ 2 + 1) ^ 2 = (-x) ^ 2 := by rw [h6]
    have h10 : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    have h11 : (-x) ^ 2 = x ^ 2 := by ring_nf
    rw [h10] at h9
    nlinarith [h9, h11]
  have h2 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := by
    field_simp [h1] at h ⊢
    <;> nlinarith
  have h3 : (y + Real.sqrt (y ^ 2 + 1)) = Real.sqrt (x ^ 2 + 1) - x := by
    have h4 : (x + Real.sqrt (x ^ 2 + 1)) ≠ 0 := by
      by_contra h5
      have h6 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 0 := by 
        rw [h5]
        norm_num
      rw [h2] at h6
      nlinarith
    have h5 : 1 / (x + Real.sqrt (x ^ 2 + 1)) = Real.sqrt (x ^ 2 + 1) - x := by 
      field_simp [h4]
      <;> nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by positivity)]
    have h8 : (y + Real.sqrt (y ^ 2 + 1)) = Real.sqrt (x ^ 2 + 1) - x := by
      rw [h] at h5
      field_simp [h1] at h5 ⊢
      <;> nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by positivity)]
    exact h8
  have h9 : (x + Real.sqrt (x ^ 2 + 1)) = Real.sqrt (y ^ 2 + 1) - y := by
    have h6 : (y + Real.sqrt (y ^ 2 + 1)) ≠ 0 := h1
    have h7 : 1 / (y + Real.sqrt (y ^ 2 + 1)) = Real.sqrt (y ^ 2 + 1) - y := by
      field_simp [h6]
      <;> nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by positivity)]
    have h10 : (x + Real.sqrt (x ^ 2 + 1)) = Real.sqrt (y ^ 2 + 1) - y := by
      rw [h] at *
      field_simp [h6] at *
      <;> nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by positivity)]
    exact h10
  nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), 
    Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by positivity), 
    h2, h3, h9]