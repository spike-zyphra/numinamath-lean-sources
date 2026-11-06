import Mathlib

theorem algebra_249007 {x y : ℕ} (h₀ : x * y = 96) (h₁ : x^2 + y^2 = 208) :
    x = 8 ∧ y = 12 ∨ x = 12 ∧ y = 8 := by
  have h2 : x ≤ 20 := by
    nlinarith [h₀, h₁]
  have h3 : y ≤ 20 := by
    nlinarith [h₀, h₁]
  interval_cases x <;> try { 
    omega
  }
  <;> interval_cases y <;> omega