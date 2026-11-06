import Mathlib

theorem algebra_85 {x₁ x₂ : ℝ} (hx₁ : x₁^2 + x₁ - 3 = 0) (hx₂ : x₂^2 + x₂ - 3 = 0)
    (hne : x₁ ≠ x₂) : x₁^3 - 4 * x₂^2 + 19 = 0 := by
  have h1 : x₁^2 = -x₁ + 3 := by linarith
  have h2 : x₁^3 = 4 * x₁ - 3 := by
    calc
      x₁^3 = x₁ * x₁^2 := by ring
      _ = x₁ * (-x₁ + 3) := by rw [h1]
      _ = -x₁^2 + 3 * x₁ := by ring
      _ = -(-x₁ + 3) + 3 * x₁ := by rw [h1]
      _ = 4 * x₁ - 3 := by ring

  have h3 : x₂^2 = -x₂ + 3 := by linarith
  have h4 : 4 * x₂^2 = -4 * x₂ + 12 := by 
    nlinarith [h3]

  have h5 : x₁ + x₂ = -1 := by 
    have h6 : x₁^2 - x₂^2 + x₁ - x₂ = 0 := by
      nlinarith [hx₁, hx₂]
    have h7 : (x₁ - x₂) * (x₁ + x₂ + 1) = 0 := by 
      nlinarith [h6]
    cases (mul_eq_zero.mp h7) with
    | inl h8 =>
      exfalso
      apply hne
      linarith
    | inr h9 =>
      linarith
  
  have h8 : x₁^3 - 4 * x₂^2 + 19 = 4 * (x₁ + x₂) + 4 := by
    linarith [h2, h4]

  rw [h8, h5]
  norm_num