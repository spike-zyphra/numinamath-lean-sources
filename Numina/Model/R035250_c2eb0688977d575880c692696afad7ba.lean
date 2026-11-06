import Mathlib

open Real Set
open scoped Real

theorem algebra_119175 {f : ℝ → ℝ} (hf : f = λ x => 3 * sin x - 4 * cos x)
  (x0 : ℝ) (hx0 : DifferentiableAt ℝ f x0) (h : ∀ x, f x ≤ f x0) :
  tan x0 = -3 / 4 := by
  have h1 : ∀ x, 3 * sin x - 4 * cos x ≤ 3 * sin x0 - 4 * cos x0 := by
    intro x
    have h2 : f x ≤ f x0 := h x
    simp [hf] at h2 ⊢
    linarith
  have h2 : 3 * sin x0 - 4 * cos x0 = 5 := by
    have h5 : 3 * sin (Real.pi - Real.arcsin (3 / 5)) - 4 * cos (Real.pi - Real.arcsin (3 / 5)) = 5 := by
      have h7 : sin (Real.pi - Real.arcsin (3 / 5)) = 3 / 5 := by
        rw [sin_pi_sub]
        rw [Real.sin_arcsin (by norm_num) (by norm_num)]
      have h8 : cos (Real.pi - Real.arcsin (3 / 5)) = -4 / 5 := by
        have h30 : cos (Real.pi - Real.arcsin (3 / 5)) = -cos (Real.arcsin (3 / 5)) := by
          rw [cos_pi_sub]
        rw [h30]
        have h31 : cos (Real.arcsin (3 / 5)) = 4 / 5 := by
          have h32 : cos (Real.arcsin (3 / 5)) = Real.sqrt (1 - (3 / 5) ^ 2) := by
            rw [Real.cos_arcsin]
          rw [h32]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith
      rw [h7, h8]
      norm_num
    have h8 : 3 * sin (Real.pi - Real.arcsin (3 / 5)) - 4 * cos (Real.pi - Real.arcsin (3 / 5)) ≤ 3 * sin x0 - 4 * cos x0 := h1 (Real.pi - Real.arcsin (3 / 5))
    nlinarith [sq_nonneg (sin x0 - 3 / 5), sq_nonneg (cos x0 + 4 / 5), Real.sin_sq_add_cos_sq x0]
  have h3 : sin x0 = 3 / 5 := by
    nlinarith [sq_nonneg (sin x0 - 3 / 5), sq_nonneg (cos x0 + 4 / 5), Real.sin_sq_add_cos_sq x0]
  have h4 : cos x0 = -4 / 5 := by
    nlinarith [sq_nonneg (sin x0 - 3 / 5), sq_nonneg (cos x0 + 4 / 5), Real.sin_sq_add_cos_sq x0]
  rw [tan_eq_sin_div_cos, h3, h4]
  all_goals norm_num