import Mathlib

theorem algebra_12184 {a b c : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 5 + a * Real.sin x ^ 3 + b * Real.sin x * Real.cos x + c * x + 4)
    (h₁ : f (-2017) = 2) :
    f 2017 = 6 := by
  have h_neg : f (-2017) = (-2017) ^ 5 + a * Real.sin (-2017) ^ 3 + b * Real.sin (-2017) * Real.cos (-2017) + c * (-2017) + 4 := h₀ (-2017)
  have simp_sin : Real.sin (-2017) = - Real.sin 2017 := Real.sin_neg 2017
  have simp_cos : Real.cos (-2017) = Real.cos 2017 := Real.cos_neg 2017
  rw [simp_sin, simp_cos] at h_neg
  have h : f 2017 = 2017 ^ 5 + a * Real.sin 2017 ^ 3 + b * Real.sin 2017 * Real.cos 2017 + c * 2017 + 4 := h₀ 2017
  rw [h_neg] at h₁
  have h2 : f 2017 = 6 := by
    linarith
  exact h2