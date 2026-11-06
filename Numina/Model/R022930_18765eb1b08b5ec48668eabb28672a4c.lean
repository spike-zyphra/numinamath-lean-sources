import Mathlib

theorem algebra_193377 (f : ℝ → ℝ → ℝ → ℝ)
    (h₀ : ∀ m n, f m n = fun x => x^2 + 2 * m * x - n^2)
    (h₁ : ∃ x₁ x₂ x₃ : ℝ, x₁ ≠ x₂ ∧ x₂ ≠ x₃ ∧ x₃ ≠ x₁ ∧
      f m n x₁ = 0 ∧ f m n x₂ = 0 ∧ f m n x₃ = 0) :
    ∃ x₀ y₀, x₀^2 + y₀^2 = 2 ∧ ∀ m n, f m n x₀ = y₀ := by

  rcases h₁ with ⟨x₁, x₂, x₃, hx12, hx23, hx31, h1, h2, h3⟩
  have eq1 : x₁^2 + 2 * m * x₁ - n^2 = 0 := by
    simp [h₀ m n] at h1 
    linarith
  have eq2 : x₂^2 + 2 * m * x₂ - n^2 = 0 := by
    simp [h₀ m n] at h2
    linarith
  have eq3 : x₃^2 + 2 * m * x₃ - n^2 = 0 := by 
    simp [h₀ m n] at h3
    linarith
  have eq4 : x₁^2 + 2 * m * x₁ = x₂^2 + 2 * m * x₂ := by
    nlinarith
  have eq5 : x₁^2 + 2 * m * x₁ = x₃^2 + 2 * m * x₃ := by 
    nlinarith 
  have eq6 : (x₁ - x₂) * (x₁ + x₂ + 2 * m) = 0 := by 
    nlinarith 
  have eq7 : x₁ + x₂ + 2 * m = 0 := by
    apply (mul_right_inj' (show x₁ - x₂ ≠ 0 by
      intro h
      apply hx12
      linarith 
    )).mp 
    linarith 
  have eq8 : (x₁ - x₃) * (x₁ + x₃ + 2 * m) = 0 := by 
    nlinarith 
  have eq9 : x₁ + x₃ + 2 * m = 0 := by 
    apply (mul_right_inj' (show x₁ - x₃ ≠ 0 by
      intro h
      apply hx31
      linarith 
    )).mp 
    linarith 
  have eq10 : x₂ = x₃ := by 
    nlinarith 
  rw [eq10] at hx23 
  contradiction