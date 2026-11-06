import Mathlib

open Real Set
open scoped Real

theorem inequalities_104642 (x : ℝ) (h : sin x > 0.9) : abs (sin (2 * x)) < 0.9 := by
  have h1 : sin (2 * x) = 2 * sin x * cos x := by
    rw [sin_two_mul]
  rw [h1]
  have h2 : sin x > 0.9 := h
  have h3 : sin x ^ 2 > (0.81 : ℝ) := by nlinarith [sq_nonneg (sin x), Real.sin_le_one x]
  have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h5 : (2 * sin x * cos x) ^ 2 < (0.81 : ℝ) := by
    have h6 : (2 * sin x * cos x) ^ 2 = 4 * (sin x ^ 2 * cos x ^ 2) := by
      ring_nf
    rw [h6]
    have h7 : sin x ^ 2 * cos x ^ 2 < (0.2025 : ℝ) := by
      have h8 : cos x ^ 2 = 1 - sin x ^ 2 := by
        linarith [h4]
      rw [h8]
      nlinarith [sq_nonneg (sin x ^ 2 - 0.81 : ℝ), sq_nonneg (sin x ^ 2 - 0.9 : ℝ), sq_nonneg (sin x - 1 : ℝ), sq_nonneg (sin x + 1 : ℝ), Real.sin_le_one x, Real.neg_one_le_sin x]
    have h9 : 4 * (sin x ^ 2 * (1 - sin x ^ 2)) < (0.81 : ℝ) := by
      nlinarith [sq_nonneg (sin x ^ 2 - 0.81 : ℝ), sq_nonneg (sin x ^ 2 - 0.9 : ℝ), sq_nonneg (sin x - 1 : ℝ), sq_nonneg (sin x + 1 : ℝ), Real.sin_le_one x, Real.neg_one_le_sin x]
    nlinarith [Real.sin_le_one x, Real.neg_one_le_sin x]
  have h10 : abs (2 * sin x * cos x) < (0.9 : ℝ) := by
    have h11 : abs (2 * sin x * cos x) = Real.sqrt ((2 * sin x * cos x) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    have h12 : Real.sqrt ((2 * sin x * cos x) ^ 2) < (0.9 : ℝ) := by
      have h13 : (2 * sin x * cos x) ^ 2 < (0.81 : ℝ) := h5
      have h14 : Real.sqrt ((2 * sin x * cos x) ^ 2) < Real.sqrt (0.81 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        · nlinarith [sq_nonneg (2 * sin x * cos x : ℝ)]
        · nlinarith
      have h15 : Real.sqrt (0.81 : ℝ) = 0.9 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      nlinarith
    linarith
  simpa using h10