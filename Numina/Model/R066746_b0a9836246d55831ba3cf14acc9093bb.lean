import Mathlib

theorem inequalities_214908 (x₁ x₂ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hsum : x₁ + x₂ = 1) :
    (x₁ + 1 / x₁) ^ 2 + (x₂ + 1 / x₂) ^ 2 ≥ 25 / 2 := by

  have h1 : 0 < x₁ * x₂ := by
    nlinarith [hsum, hx₁, hx₂]

  have h3 : (x₁ + 1 / x₁) ^ 2 + (x₂ + 1 / x₂) ^ 2 =
      x₁^2 + x₂^2 + 4 + 1 / x₁^2 + 1 / x₂^2 := by
    field_simp [hx₁.ne.symm, hx₂.ne.symm]
    <;> ring

  rw [h3]

  have h4 : x₁^2 + x₂^2 ≥ 2 * (x₁ * x₂) := by
    nlinarith [sq_nonneg (x₁ - x₂)]

  have h5 : x₁ * x₂ ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (x₁ - 1 / 2), sq_nonneg (x₂ - 1 / 2), hsum]

  have h6 : (1 / x₁ ^ 2) + (1 / x₂ ^ 2) ≥ 8 := by
    have h7 : (1 / x₁ ^ 2) + (1 / x₂ ^ 2) - (8 : ℝ) ≥ 0 := by
      have h8 : (1 / x₁ ^ 2) + (1 / x₂ ^ 2) - (8 : ℝ) =
          (x₁^2 + x₂^2 - 8 * (x₁ * x₂)^2) / (x₁^2 * x₂^2) := by
        field_simp [hx₁.ne.symm, hx₂.ne.symm]
        <;> nlinarith
      rw [h8]
      have h9 : x₁^2 * x₂^2 > 0 := by
        nlinarith [h1]
      have h10 : x₁ ^ 2 + x₂ ^ 2 - 8 * (x₁ * x₂)^2 ≥ 0 := by
        nlinarith [sq_nonneg (x₁ * x₂ - 1 / 2), sq_nonneg (x₁ - x₂),
          h4, h5, mul_pos hx₁ hx₂, sq_nonneg (x₁ * x₂), sq_nonneg (x₁ - 1 / 2), sq_nonneg (x₂ - 1 / 2), hsum]
      have h11 : (x₁ ^ 2 + x₂ ^ 2 - 8 * (x₁ * x₂)^2) / (x₁^2 * x₂^2) ≥ 0 := by
        apply div_nonneg
        linarith
        all_goals { nlinarith [h9] }
      linarith
    linarith

  have h8 : x₁^2 + x₂^2 ≥ 1 / 2 := by
    nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 1), hsum, mul_pos hx₁ hx₂]

  nlinarith [h8, h6]