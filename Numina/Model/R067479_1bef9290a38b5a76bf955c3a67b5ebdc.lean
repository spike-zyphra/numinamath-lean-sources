import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_215599 {f : ℝ → ℝ} (hf : f = λ x => x * sin x)
  (x₀ : ℝ) (hx₀ : Differentiable ℝ f) (h : deriv f x₀ = 0) :
  (1 + x₀^2) * (1 + cos (2 * x₀)) = 2 := by
    have hf' : deriv f x₀ = sin x₀ + x₀ * cos x₀ := by
      rw [hf]
      simp [deriv_mul, deriv_id'', mul_comm]
      all_goals try linarith
      all_goals try simp [Real.differentiableAt_sin]
      all_goals try tauto
    rw [hf'] at h
    have h1 : sin x₀ = -x₀ * cos x₀ := by
      linarith
    have h2 : sin x₀ ^ 2 + cos x₀ ^ 2 = 1 := Real.sin_sq_add_cos_sq x₀
    rw [h1] at h2
    have h3 : cos x₀ ^ 2 = 1 / (1 + x₀^2) := by
      field_simp [(show 1 + x₀^2 ≠ 0 by nlinarith)]
      nlinarith
    have h4 : 1 + cos (2 * x₀) = 2 * cos x₀ ^ 2 := by
      have hcos2 : cos (2 * x₀) = 2 * cos x₀ ^ 2 - 1 := by
        rw [cos_two_mul]
        all_goals try nlinarith
      linarith [hcos2]
    rw [h4]
    rw [h3]
    field_simp [(show 1 + x₀^2 ≠ 0 by nlinarith)]
    <;> nlinarith
    all_goals try linarith
    all_goals try nlinarith