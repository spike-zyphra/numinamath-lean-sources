import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_172203 {A B : ℝ} (h : ∀ x ∈ Icc 0 (3 * π / 2), |cos x ^ 2 + 2 * sin x * cos x - sin x ^ 2 + A * x + B| ≤ 1) :
    A = 0 ∧ B = 0 := by
  have h1 := h 0 (by
    constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
  )
  have h2 := h (π / 2) (by
    constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
  )
  have h3 := h π (by
    constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
  )
  have h4 := h (3 * π / 2) (by
    constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
  )
  have h5 := h (π / 4) (by
    constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
  )
  have h6 := h (3 * π / 4) (by
    constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
  )
  have h7 := h (5 * π / 4) (by
    constructor <;> nlinarith [pi_pos, Real.pi_gt_three]
  )
  norm_num [abs_le] at h1 h2 h3 h4 h5 h6 h7
  constructor
  · nlinarith [Real.sin_sq_add_cos_sq (0 : ℝ), Real.sin_sq_add_cos_sq (π / 2 : ℝ), Real.sin_sq_add_cos_sq (π : ℝ), Real.sin_sq_add_cos_sq (3 * π / 2 : ℝ), Real.sin_sq_add_cos_sq (π / 4 : ℝ), Real.sin_sq_add_cos_sq (3 * π / 4 : ℝ), Real.sin_sq_add_cos_sq (5 * π / 4 : ℝ), Real.pi_gt_three]
  · nlinarith [Real.sin_sq_add_cos_sq (0 : ℝ), Real.sin_sq_add_cos_sq (π / 2 : ℝ), Real.sin_sq_add_cos_sq (π : ℝ), Real.sin_sq_add_cos_sq (3 * π / 2 : ℝ), Real.sin_sq_add_cos_sq (π / 4 : ℝ), Real.sin_sq_add_cos_sq (3 * π / 4 : ℝ), Real.sin_sq_add_cos_sq (5 * π / 4 : ℝ), Real.pi_gt_three]