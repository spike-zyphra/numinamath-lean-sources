import Mathlib

open Real

theorem algebra_609539 : tan (π / 7) * tan (2 * π / 7) * tan (3 * π / 7) = √7 := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
  field_simp
  have h₁ : cos (π / 7) * cos (2 * π / 7) * cos (3 * π / 7) = 1 / 8 := by
    set θ := π / 7 with hθ
    rw [show 2 * π / 7 = 2 * θ by linarith, show 3 * π / 7 = 3 * θ by linarith]
    suffices 8 * cos θ * cos (2 * θ) * cos (3 * θ) - 1 = 0 by linarith
    have h₁ : sin (7 * θ) = sin (4 * θ) * cos (3 * θ) + cos (4 * θ) * sin (3 * θ) := by
      rw [←sin_add]; ring_nf
    have h₂ : sin (4 * θ) = 4 * sin θ * cos θ * cos (2 * θ) := by
      rw [show 4 * θ = 2 * (2 * θ) by ring_nf, sin_two_mul]
      field_simp
      rw [sin_two_mul]
      apply Or.inl
      ring_nf
    have h₃ : sin (3 * θ) = sin θ * (2 * cos θ ^ 2 + cos (2 * θ)) := by
      rw [show 3 * θ = θ + 2 * θ by ring_nf, sin_add, sin_two_mul]
      ring_nf
    have h₄ : sin (7 * θ) = sin θ * (4 * cos θ * cos (2 * θ) * cos (3 * θ) + cos (4 * θ) * (2 * cos θ ^ 2 + cos (2 * θ))) := by
      rw [h₁, h₂, h₃]
      ring_nf
    have h₇ : cos (4 * θ) * (2 * cos θ ^ 2 + cos (2 * θ)) = 4 * cos θ * cos (2 * θ) * cos (3 * θ) - 1 := by
      have h₅ : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
        rw [show 4 * θ = 2 * (2 * θ) by ring_nf, cos_two_mul]
      have : cos (4 * θ) = 8 * cos θ ^ 4 - 8 * cos θ ^ 2 + 1 := by
        rw [h₅, cos_two_mul]
        ring_nf
      rw [this, cos_three_mul θ, cos_two_mul]
      ring_nf
    have h₅ : 4 * cos θ * cos (2 * θ) * cos (3 * θ) + cos (4 * θ) * (2 * cos θ ^ 2 + cos (2 * θ)) = 8 * cos θ * cos (2 * θ) * cos (3 * θ) - 1 := by linarith
    have h₆ : sin (7 * θ) = 0 := by
      rw [hθ]
      ring_nf
      exact sin_pi
    rw [h₅, h₆] at h₄
    simp at h₄
    obtain (h₄ | h₄) := h₄
    · -- sin θ = 0, which is impossible
      rw [sin_eq_zero_iff] at h₄
      obtain ⟨k, hk₁⟩ := h₄
      rw [hθ] at hk₁
      field_simp at hk₁
      rw [mul_assoc, mul_comm, mul_assoc] at hk₁
      field_simp at hk₁
      norm_cast at hk₁
      omega
    · linarith
  rw [h₁]
  field_simp

  have h₂ : sin (π / 7) * sin (2 * π / 7) * sin (3 * π / 7) = √7 / 8 := by
    obtain ⟨θ, hθ⟩ := show ∃ θ, θ = π / 7 by simp
    rw [←hθ, show 2 * π / 7 = 2 * θ by linarith, show 3 * π / 7 = 3 * θ by linarith]
    have h₁ : -sin (7 * θ) = 64 * sin θ ^ 7 - 112 * sin θ ^ 5 + 56 * sin θ ^ 3 - 7 * sin θ := by
      rw [show 7 * θ = (2 * (3 * θ) + θ) by linarith, sin_add, sin_two_mul, cos_two_mul]
      rw [sin_three_mul, cos_three_mul]
      ring_nf
      have : cos θ ^ 6 = (1 - sin θ ^ 2) ^ 3 := by rw [←cos_sq']; ring_nf
      rw [this]
      have : cos θ ^ 4 = (1 - sin θ ^ 2) ^ 2 := by rw [←cos_sq']; ring_nf
      rw [this, cos_sq']
      ring_nf
    have h₂ : sin (7 * θ) = 0 := by
      rw [hθ]
      ring_nf
      exact sin_pi
    rw [h₂] at h₁
    suffices (sin θ * sin (2 * θ) * sin (3 * θ))^2 = (√7 / 8)^2 by
      rw [sq_eq_sq₀ ?_ (by positivity)] at this
      exact this
      apply mul_nonneg
      apply mul_nonneg
      all_goals {
        rw [hθ]
        apply sin_nonneg_of_nonneg_of_le_pi
        positivity
        ring_nf
        bound
      }

    set s := sin θ with hs
    have h₃ : s * (64 * s ^ 6 - 112 * s ^ 4 + 56 * s ^ 2 - 7) = 0 := by ring_nf; linarith
    simp at h₃
    obtain (h₃ | h₃) := h₃
    · rw [hs, sin_eq_zero_iff] at h₃
      obtain ⟨k, hk₁⟩ := h₃
      rw [hθ] at hk₁
      field_simp at hk₁
      rw [mul_assoc, mul_comm, mul_assoc] at hk₁
      field_simp at hk₁
      norm_cast at hk₁
      omega
    · have : (√7 / 8) ^ 2 = 7 / 64 := by
        ring_nf
        rw [sq_sqrt]
        repeat linarith
      rw [sin_two_mul, sin_three_mul, ←hs, this]
      ring_nf
      rw [cos_sq', ←hs]
      ring_nf
      obtain ⟨x, hx⟩ := show ∃ x, x = s ^ 2 by simp
      rw [show s ^ 4 = x ^ 2 by rw [hx]; ring_nf] at h₃
      rw [show s ^ 6 = x ^ 3 by rw [hx]; ring_nf] at h₃ ⊢
      rw [show s ^ 8 = x ^ 3 * x by rw [hx]; ring_nf]
      rw [show s ^ 10 = x ^ 3 * x^2 by rw [hx]; ring_nf]
      rw [show s ^ 12 = x ^ 3 * x^3 by rw [hx]; ring_nf]
      have hx₁ : x^3 = (112 * x^2 - 56 * x + 7) / 64 := by linarith
      rw [hx₁]
      ring_nf
      rw [show x ^ 4 = x^3 * x by rw [hx]; ring_nf, hx₁]
      ring_nf
      linarith

  rw [h₂]
  field_simp
