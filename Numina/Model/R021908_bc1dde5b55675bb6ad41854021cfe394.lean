import Mathlib

theorem algebra_121500 (a b c d : ℤ) (h : ∀ m n : ℤ, ∃ x y : ℤ,
    a * x + b * y = m ∧ c * x + d * y = n) :
    a * d - b * c = 1 ∨ a * d - b * c = -1 := by
  have eq4 := h 1 0
  rcases eq4 with ⟨x₁, y₁, h1₁, h1₂⟩
  have eq5 := h 0 1
  rcases eq5 with ⟨x₂, y₂, h2₁, h2₂⟩
  have h3 : (a * d - b * c) * (x₁ * y₂ - x₂ * y₁) = 1 := by
    have eq1 : a * x₁ + b * y₁ = 1 := by linarith
    have eq2 : c * x₁ + d * y₁ = 0 := by linarith
    have eq3 : a * x₂ + b * y₂ = 0 := by linarith
    have eq4 : c * x₂ + d * y₂ = 1 := by linarith
    nlinarith [sq_nonneg (a * y₂ - b * x₂), sq_nonneg (c * y₁ - d * x₁),
      sq_nonneg (a * x₁ + b * y₁ - 1), sq_nonneg (c * x₁ + d * y₁), 
      sq_nonneg (a * x₂ + b * y₂), sq_nonneg (c * x₂ + d * y₂ - 1)]
  have h4 : a * d - b * c = 1 ∨ a * d - b * c = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h3
  exact h4