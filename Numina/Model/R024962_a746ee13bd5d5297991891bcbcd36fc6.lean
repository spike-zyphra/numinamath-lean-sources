import Mathlib

open Real Set
open scoped Real

theorem calculus_319466 (θ : Real) (hθ : θ ∈ Ioo 0 (π/2)) (f : ℝ → ℝ)
  (hf : f = λ θ => cos θ + θ * sin θ) :
  f θ > 1 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have h1 : f θ = cos θ + θ * sin θ := by
    rw [hf]
  rw [h1]
  have h2 : 0 < θ := hθ1
  have h3 : θ < Real.pi / 2 := hθ2
  have h4 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, h2, h3]
    · linarith [Real.pi_pos, h2, h3]
  have h5 : sin θ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos, h2, h3]
    · linarith [Real.pi_pos, h2, h3]
  have h6 : cos θ + θ * sin θ > 1 := by
    by_contra h
    push_neg at h
    have h10 : cos θ + θ * sin θ - 1 ≤ 0 := by linarith
    have h11 : cos θ + θ * sin θ - 1 > 0 := by
      have h9 : 0 < θ := h2
      have h10 : θ < Real.pi / 2 := h3
      have h21 : cos θ > 0 := h4
      have h22 : sin θ > 0 := h5
      have h23 : sin θ < θ := by
        apply sin_lt
        all_goals linarith [Real.pi_pos, h2, h3]
      have h24 : cos θ < 1 := by
        have hcos : cos θ < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [Real.pi_pos, h2, h3]
        have hcos2 : cos (0 : ℝ) = 1 := Real.cos_zero
        linarith [hcos, hcos2]
      have h25 : θ * cos θ > 0 := by
        apply mul_pos
        · linarith
        · linarith
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos h2, sq_nonneg (θ ^ 2 - 1), sq_nonneg (sin θ - θ), sq_nonneg (cos θ - 1), Real.sin_sq_add_cos_sq θ, mul_pos h2 h4, mul_pos h2 h5, Real.sin_le_one θ, Real.cos_le_one θ, sq_nonneg (cos θ - sin θ), sq_nonneg (θ - sin θ), sq_nonneg (θ - cos θ), Real.sin_sq_add_cos_sq θ]
    linarith
  linarith