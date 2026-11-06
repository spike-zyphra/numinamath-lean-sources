import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_258620 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * sin (3 * x) + 3 * sin x + 3 * sqrt 3 * cos x)
  (h₁ : x ∈ Icc 0 Real.pi) :
  f x ∈ Icc (-3 * sqrt 3) 8 := by
  rcases h₁ with ⟨hx0, hxpi⟩
  have h4 : f x = 2 * sin (3 * x) + 3 * sin x + 3 * sqrt 3 * cos x := h₀ x
  rw [h4]
  have h13 : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
    rw [sin_three_mul]
    <;> ring
  have h15 : sin x ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith
    linarith
  have h17 : cos x ≤ 1 := by
    linarith [cos_le_one x]
  have h18 : -1 ≤ cos x := by
    linarith [neg_one_le_cos x]
  have h7 : -3 * sqrt 3 ≤ 2 * sin (3 * x) + 3 * sin x + 3 * sqrt 3 * cos x := by
    rw [h13]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      sq_nonneg (sin x - 1 / 2), sq_nonneg (cos x + 1 / 2), sq_nonneg (sin x ^ 2 - 1 / 4), sq_nonneg (cos x - Real.sqrt 3 / 2), sq_nonneg (sin x - 1), sq_nonneg (cos x + 1), h15, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
        Real.sqrt_nonneg (3 : ℝ), sin_sq_add_cos_sq x]
  have h8 : 2 * sin (3 * x) + 3 * sin x + 3 * sqrt 3 * cos x ≤ 8 := by
    rw [h13]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      sq_nonneg (sin x - 1 / 2), sq_nonneg (cos x - Real.sqrt 3 / 2), sq_nonneg (sin x - 1), sq_nonneg (cos x + 1), h15, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
        Real.sqrt_nonneg (3 : ℝ), sin_sq_add_cos_sq x]
  constructor
  · nlinarith
  · nlinarith