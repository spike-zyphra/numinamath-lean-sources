import Mathlib

theorem algebra_13756 {f : ℝ → ℝ → ℝ} (hf : ∀ a b, f a b = (Real.sqrt (2 * a + b)) ^ 3)
    (x : ℝ) (hx : f 4 x = 27) : x = 1 := by
  have h1 : f 4 x = (Real.sqrt (2 * (4 : ℝ) + x)) ^ 3 := hf 4 x
  rw [h1] at hx
  have h2 : (Real.sqrt (2 * (4 : ℝ) + x)) ^ 3 = 27 := by 
    linarith
  have h3 : Real.sqrt (2 * (4 : ℝ) + x) = 3 := by 
    have h4 : Real.sqrt (2 * (4 : ℝ) + x) ≥ 0 := by 
      apply Real.sqrt_nonneg
    have h5 : (Real.sqrt (2 * (4 : ℝ) + x)) ^ 3 - 27 = 0 := by
      linarith
    have h6 : (Real.sqrt (2 * (4 : ℝ) + x)) ^ 3 - 27 = (Real.sqrt (2 * (4 : ℝ) + x) - 3) * ((Real.sqrt (2 * (4 : ℝ) + x)) ^ 2 + 3 * (Real.sqrt (2 * (4 : ℝ) + x)) + 9) := by
      ring
    rw [h6] at h5
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case where Real.sqrt (2 * (4 : ℝ) + x) - 3 = 0
      linarith
    · -- Case where (Real.sqrt (2 * (4 : ℝ) + x)) ^ 2 + 3 * (Real.sqrt (2 * (4 : ℝ) + x)) + 9 = 0
      nlinarith [sq_nonneg (Real.sqrt (2 * (4 : ℝ) + x) + 3 / 2), Real.sqrt_nonneg (2 * (4 : ℝ) + x)]
  have h6 : Real.sqrt (2 * (4 : ℝ) + x) = 3 := h3
  have h7 : 2 * (4 : ℝ) + x ≥ 0 := by 
    by_contra h
    push_neg at h
    have h8 : Real.sqrt (2 * (4 : ℝ) + x) = 0 := by 
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
    rw [h8] at h6 
    all_goals nlinarith
  have h4 : 2 * (4 : ℝ) + x = 9 := by 
    have h8 : (Real.sqrt (2 * (4 : ℝ) + x)) ^ 2 = (3 : ℝ) ^ 2 := by 
      rw [show Real.sqrt (2 * (4 : ℝ) + x) = (3 : ℝ) by linarith [h6]]
    have h9 : (Real.sqrt (2 * (4 : ℝ) + x)) ^ 2 = 2 * (4 : ℝ) + x := by 
      rw [Real.sq_sqrt]
      linarith
    rw [h9] at h8 
    linarith
  linarith