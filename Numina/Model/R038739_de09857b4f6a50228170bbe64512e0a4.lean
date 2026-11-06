import Mathlib

open Real


theorem algebra_609133 (a b : ℝ) (h: (a*b)/(a^2 + b^2) = 1/4) : (abs (a^2-b^2))/(a^2 + b^2) = sqrt 3 / 2 := by
  have hp: (a ≠ 0) ∧ (b ≠ 0) := by
    constructor
    by_contra! ha; rw [ha] at h; norm_num at h
    by_contra! hb; rw [hb] at h; norm_num at h
  have hq: a^2 + b^2 > 0 := by
    have : a^2 > 0 := by apply sq_pos_of_ne_zero hp.left
    have : b^2 > 0 := by apply sq_pos_of_ne_zero hp.right
    linarith
  have h1: 4*a*b = a^2 + b^2 := by
    have h1 := h
    have : a^2 + b^2 ≠ 0 := by linarith
    field_simp at h1
    linarith
  have h2: (a^2 - b^2)^2 = 3/4 * (a^2 + b^2)^2 := by
    have h11 : a^2 + b^2 = 4 * a * b := by linarith
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * b), sq_pos_of_pos (show 0 < 4 by linarith)]
  have h3: abs (a^2 - b^2) = Real.sqrt 3 / 2 * (a^2 + b^2) := by
    have h4 : abs (a^2 - b^2) = Real.sqrt ((a^2 - b^2)^2) := by
      rw [Real.sqrt_sq_eq_abs]
    have h5 : Real.sqrt ((a^2 - b^2)^2) = Real.sqrt (3/4 * (a^2 + b^2)^2) := by
      rw [h2]
    have h6 : Real.sqrt (3/4 * (a^2 + b^2)^2) = Real.sqrt (3/4) * Real.sqrt ((a^2 + b^2)^2) := by 
      rw [Real.sqrt_mul (by positivity)]
    have h7 : Real.sqrt ((a^2 + b^2)^2) = a^2 + b^2 := by
      apply Real.sqrt_sq (by positivity)
    have h8 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h4, h5, h6, h7, h8]
  calc
    (abs (a^2 - b^2)) / (a^2 + b^2) = (Real.sqrt 3 / 2 * (a^2 + b^2)) / (a^2 + b^2) := by 
      rw [h3]
    _ = Real.sqrt 3 / 2 := by
      field_simp [hq]
      <;> ring