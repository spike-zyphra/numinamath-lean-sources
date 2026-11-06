import Mathlib

open Real Set
open scoped Real

theorem algebra_191227 {f : ℝ → ℝ} (hf : f = λ x => sin x ^ 6 + cos x ^ 6) :
    IsLeast (range f) (1 / 4) ∧ IsGreatest (range f) 1 := by
  have h1 : ∀ x, f x = sin x ^ 6 + cos x ^ 6 := by
    intro x
    rw [hf]

  constructor
  · -- Show that 1/4 is the least element in the range of f
    constructor
    · -- Show that 1/4 is in the range of f
      use Real.pi / 4
      rw [h1]
      have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h3 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      rw [h2, h3]
      have h4 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h5 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 3 := by ring
      rw [h5, h4]
      norm_num
    · -- Show that 1/4 is the least element
      intro y hy
      rcases hy with ⟨x, hx⟩
      rw [h1] at hx
      have h2 : sin x ^ 2 + cos x ^ 2 = 1 := by
        have h := Real.sin_sq_add_cos_sq x
        linarith
      nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x * cos x), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
  · -- Show that 1 is the greatest element in the range of f
    constructor
    · -- Show that 1 is in the range of f
      use (0 : ℝ)
      rw [h1]
      norm_num [Real.sin_zero, Real.cos_zero]
    · -- Show that 1 is the greatest element
      intro y hy
      rcases hy with ⟨x, hx⟩
      rw [h1] at hx
      have h2 : sin x ^ 2 + cos x ^ 2 = 1 := by
        have h := Real.sin_sq_add_cos_sq x
        linarith
      nlinarith [sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos x ^ 2 - 1), sq_nonneg (sin x), sq_nonneg (cos x), sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x * cos x), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1)]