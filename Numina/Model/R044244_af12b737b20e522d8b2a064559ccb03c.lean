import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_249073 (a b c : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * sin x + b * cos x + c)
  (h₁ : f 0 = 5) (h₂ : f (π/2) = 5) (h₃ : ∀ x ∈ Icc 0 (π/2), |f x| ≤ 10) :
  -5 * sqrt 2 ≤ c ∧ c ≤ 15 * sqrt 2 + 20 := by
  have h1 : f 0 = a * sin 0 + b * cos 0 + c := h₀ 0
  rw [h1] at h₁
  have h2 : sin 0 = 0 := by simp
  have h3 : cos 0 = 1 := by simp
  rw [h2, h3] at h₁
  have eq1 : b = 5 - c := by linarith
  -- Apply at x = π/2
  have h4 : f (π/2) = a * sin (π/2) + b * cos (π/2) + c := h₀ (π/2)
  rw [h4] at h₂
  have h5 : sin (π/2) = 1 := by rw [sin_pi_div_two]
  have h6 : cos (π/2) = 0 := by rw [cos_pi_div_two]
  rw [h5, h6] at h₂
  have eq2 : a = 5 - c := by linarith
  -- apply at x = π/4
  have h7 := h₃ (Real.pi / 4) (by
    constructor <;> linarith [Real.pi_pos]
  )
  have h8 : f (Real.pi / 4) = a * sin (Real.pi / 4) + b * cos (Real.pi / 4) + c := h₀ (Real.pi / 4)
  have h51 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [sin_pi_div_four]
  have h52 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [cos_pi_div_four]
  rw [h8] at h7
  rw [h51, h52] at h7
  rw [eq1, eq2] at h7
  have h9 : -10 ≤ (5 - c) * Real.sqrt 2 + c := by
    cases abs_le.mp h7 with
    | intro h10 h11 =>
      linarith
  have h10 : (5 - c) * Real.sqrt 2 + c ≤ 10 := by
    cases abs_le.mp h7 with
    | intro h10 h11 =>
      linarith
  have h11 : -5 * Real.sqrt 2 ≤ c := by
    nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
  have h12 : c ≤ 15 * Real.sqrt 2 + 20 := by
    nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
  constructor <;> linarith [h11, h12]