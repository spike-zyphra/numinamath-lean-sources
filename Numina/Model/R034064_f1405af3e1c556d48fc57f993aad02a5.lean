import Mathlib

theorem algebra_194063 (x : ℝ) (hx : x ≥ 0) :
    2 * (x - 6) = x ^ 2 / (1 + Real.sqrt (x + 1)) ^ 2 ↔ x = 8 := by
  constructor
  · -- Forward direction: If the equation holds, then x = 8
    intro h_eq
    have h1 : 0 ≤ (x + 1 : ℝ) := by linarith
    have h2 : Real.sqrt (x + 1) ≥ 0 := by apply Real.sqrt_nonneg
    have h3 : (1 + Real.sqrt (x + 1)) ^ 2 > 0 := by
      have h4 : 1 + Real.sqrt (x + 1) > 0 := by
        have h5 : Real.sqrt (x + 1) ≥ 0 := by apply Real.sqrt_nonneg
        by_contra h6
        push_neg at h6
        have h7 : Real.sqrt (x + 1) ≤ -1 := by linarith
        have h8 : Real.sqrt (x + 1) ≥ 0 := by apply Real.sqrt_nonneg
        linarith
      positivity
    have h4 : 2 * (x - 6) * (1 + Real.sqrt (x + 1)) ^ 2 = x ^ 2 := by
      have h5 : x ^ 2 / (1 + Real.sqrt (x + 1)) ^ 2 = x ^ 2 / (1 + Real.sqrt (x + 1)) ^ 2 := by rfl
      field_simp [(show (1 + Real.sqrt (x + 1)) ^ 2 ≠ 0 by positivity)] at h_eq ⊢
      <;> linarith
    have h5 : Real.sqrt (x + 1) ≥ 0 := by positivity
    have h6 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (show (x + 1 : ℝ) ≥ 0 by linarith)
    nlinarith [sq_nonneg (x - 8), sq_nonneg (Real.sqrt (x + 1) - 3), 
      sq_nonneg (Real.sqrt (x + 1) + 1), 
      h6, Real.sqrt_nonneg (x + 1)]
  · -- Backward direction: If x = 8, then the equation holds
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (8 + 1) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h1]
    norm_num
    <;> ring_nf <;> norm_num
    all_goals linarith