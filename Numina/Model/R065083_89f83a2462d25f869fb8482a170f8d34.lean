import Mathlib

theorem algebra_296674 {b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x ^ 2 + b * x + c)
    (x₁ x₂ : ℝ) (hx₁ : f x₁ = f x₂) (hx₂ : x₁ ≠ x₂) :
    ∀ x, f x = f (x₁ + x₂ - x) := by
  -- Assume f(x₁) = f(x₂)
  -- From definition of f, expanding gives
  -- $f(x₁) = 2x₁² + bx₁ + c$
  -- $f(x₂) = 2x₂² + bx₂ + c$
  intro x
  have eq1 : f x₁ = 2 * x₁ ^ 2 + b * x₁ + c := hf x₁
  have eq2 : f x₂ = 2 * x₂ ^ 2 + b * x₂ + c := hf x₂
  rw [eq1] at hx₁
  rw [eq2] at hx₁
  
  have eq3 : f (x₁ + x₂ - x) = 2 * (x₁ + x₂ - x) ^ 2 + b * (x₁ + x₂ - x) + c := hf (x₁ + x₂ - x)
  have eq4 : f x = 2 * x ^ 2 + b * x + c := hf x
  
  rw [eq4, eq3]

  have h_eq : 2 * (x₁ + x₂) + b = 0 := by
    have h1 : 2 * (x₁ ^ 2 - x₂ ^ 2) + b * (x₁ - x₂) = 0 := by
      nlinarith
    have h2 : (x₁ - x₂) * (2 * (x₁ + x₂) + b) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.mp h2) with hx hx
    · -- Case where $x₁ - x₂ = 0$, which contradicts $x₁ ≠ x₂$
      exfalso
      exact hx₂ (by linarith)
    · -- Case where $2(x₁ + x₂) + b = 0$ which is the desired equation
      linarith
  
  have hb : b = -2 * (x₁ + x₂) := by linarith
  
  rw [hb]
  all_goals
    nlinarith [sq_nonneg (x - (x₁ + x₂) / 2)]