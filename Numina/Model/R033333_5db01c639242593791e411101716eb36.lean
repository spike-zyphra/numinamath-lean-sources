import Mathlib

theorem algebra_174123 {c : ℝ} (h : ∃ x y, x^2-3*x+c=0 ∧ y^2+3*y-c=0 ∧ x=-y) :
    x^2-3*x+c=0 ↔ x=0 ∨ x=3 := by
  rcases h with ⟨x₀, y₀, h_eq1, h_eq2, h_eq3⟩
  have eq1 : y₀ = -x₀ := by linarith
  rw [eq1] at h_eq2
  -- Now h_eq1 is x₀^2 - 3*x₀ + c = 0 and h_eq2 is (-x₀)^2 + 3*(-x₀) - c = 0
  -- Simplifying h_eq2: x₀^2 - 3*x₀ - c = 0
  have hx00 : x₀ * (x₀ - 3) = 0 := by 
    nlinarith
  have hx01 : x₀ = 0 ∨ x₀ = 3 := by 
    cases (mul_eq_zero.mp hx00) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  -- Now we know that c = 0.
  have hc00 : c = 0 := by 
    cases hx01 with
    | inl h1 => 
      rw [h1] at h_eq1
      nlinarith
    | inr h2 => 
      rw [h2] at h_eq1
      nlinarith
  -- Now proving the main theorem, which direction.
  constructor
  · -- Assume x^2 - 3*x + c = 0, prove x = 0 ∨ x = 3
    intro h_eq
    have eq3 : x ^ 2 - 3 * x = 0 := by 
      nlinarith [h_eq, hc00]
    have eq4 : x * (x - 3) = 0 := by 
      nlinarith [eq3]
    cases (mul_eq_zero.mp eq4) with
    | inl h1 =>
      left
      linarith
    | inr h2 =>
      right
      linarith
  · -- Assume x = 0 ∨ x = 3, prove x^2 - 3*x + c = 0
    rintro (h_eq | h_eq)
    · -- Case x = 0
      rw [h_eq]
      nlinarith [hc00]
    · -- Case x = 3
      rw [h_eq]
      nlinarith [hc00]