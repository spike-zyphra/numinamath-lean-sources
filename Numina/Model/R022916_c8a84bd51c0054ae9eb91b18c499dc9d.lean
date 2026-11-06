import Mathlib

theorem algebra_162666 (a b : ℝ) (h : a * b / (a ^ 2 + b ^ 2) = 1 / 4) :
    |a ^ 2 - b ^ 2| / (a ^ 2 + b ^ 2) = Real.sqrt 3 / 2 := by
  have h1 : a ^ 2 + b ^ 2 > 0 := by
    by_contra h2
    push_neg at h2
    have h3 : a ^ 2 ≥ 0 := sq_nonneg a
    have h4 : b ^ 2 ≥ 0 := sq_nonneg b
    have h5 : a ^ 2 = 0 := by nlinarith
    have h6 : b ^ 2 = 0 := by nlinarith
    have h7 : a = 0 := by nlinarith
    have h8 : b = 0 := by nlinarith
    rw [h7, h8] at h
    norm_num at h
    all_goals linarith
  have h2 : 4 * (a * b) = a ^ 2 + b ^ 2 := by
    have h3 : a ^ 2 + b ^ 2 ≠ 0 := by positivity
    field_simp at h
    nlinarith
  have h3 : (a ^ 2 - b ^ 2) ^ 2 = (3 / 4) * (a ^ 2 + b ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b)]
  have h4 : |a ^ 2 - b ^ 2| = Real.sqrt 3 / 2 * (a ^ 2 + b ^ 2) := by
    have h5 : (a ^ 2 - b ^ 2) ^ 2 = (3 / 4) * (a ^ 2 + b ^ 2) ^ 2 := h3
    have h6 : |a ^ 2 - b ^ 2| = Real.sqrt ((a ^ 2 - b ^ 2) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    have h7 : Real.sqrt ((3 / 4) * (a ^ 2 + b ^ 2) ^ 2) = Real.sqrt 3 / 2 * (a ^ 2 + b ^ 2) := by
      have h8 : (a ^ 2 + b ^ 2) ≥ 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have h9 : Real.sqrt ((3 / 4) * (a ^ 2 + b ^ 2) ^ 2) = Real.sqrt (3 / 4) * Real.sqrt ((a ^ 2 + b ^ 2) ^ 2) := by
        rw [Real.sqrt_mul (by positivity)]
      have h10 : Real.sqrt ((a ^ 2 + b ^ 2) ^ 2) = (a ^ 2 + b ^ 2) := by
        rw [Real.sqrt_sq (show (a ^ 2 + b ^ 2) ≥ 0 by nlinarith [sq_nonneg a, sq_nonneg b, h1])]
      have h11 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h9, h10, h11]
      all_goals nlinarith [Real.sqrt_nonneg (3 / 4 : ℝ), Real.sqrt_nonneg ((a ^ 2 + b ^ 2) ^ 2), Real.sqrt_nonneg 3, h1]
    rw [h6]
    rw [h5]
    rw [h7]
    all_goals nlinarith [Real.sqrt_nonneg ((a ^ 2 - b ^ 2) ^ 2), Real.sqrt_nonneg ((3 / 4) * (a ^ 2 + b ^ 2) ^ 2), Real.sqrt_nonneg 3, h1]
  have h5 : |a ^ 2 - b ^ 2| / (a ^ 2 + b ^ 2) = Real.sqrt 3 / 2 := by
    rw [h4]
    field_simp [show a ^ 2 + b ^ 2 > 0 by linarith [h1]]
    all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), h1]
  exact h5