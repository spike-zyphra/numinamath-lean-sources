import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_126332 {a : ℝ} (h : ∃ x : ℝ, sin x ^ 2 - (2 * a + 1) * cos x - a ^ 2 = 0) :
    a ∈ Icc (-5 / 4) (1 + sqrt 2) := by
  rcases h with ⟨x, hx⟩
  have h1 : sin x ^ 2 = 1 - cos x ^ 2 := by
    rw [Real.sin_sq]
  rw [h1] at hx
  have h2 : cos x ^ 2 + (2 * a + 1) * cos x + (a ^ 2 - 1) = 0 := by
    nlinarith
  have h3 : -1 ≤ cos x ∧ cos x ≤ 1 := by
    constructor
    · linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
    · linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
  rcases h3 with ⟨h4, h5⟩
  have h6 : a ≥ -5 / 4 := by
    nlinarith [sq_nonneg (cos x + (2 * a + 1) / 2), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (a + 5 / 4), Real.sin_sq_add_cos_sq x, sq_nonneg (a + 5 / 4)]
  have h7 : a ≤ 1 + Real.sqrt 2 := by
    nlinarith [sq_nonneg (cos x + 1), sq_nonneg (a - (1 + Real.sqrt 2)), sq_nonneg (cos x - (- (2 * a + 1) / 2 - Real.sqrt (4 * a + 5) / 2  )), sq_nonneg (cos x - (- (2 * a + 1) / 2 + Real.sqrt (4 * a + 5) / 2  )), sq_nonneg (a + 5 / 4), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), sq_nonneg (cos x - 1), Real.sin_sq_add_cos_sq x, sq_nonneg (a - (1 + sqrt 2)), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
  constructor
  · linarith
  · linarith