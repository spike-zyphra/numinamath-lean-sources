import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10984 {a : ℝ} (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x ^ 3 + (a + 1) * x ^ 2 + (a + 1) * x + a)
  (h₁ : ∃ x₁ x₂, x₁ ≠ x₂ ∧ f x₁ = f x₂) :
  a > 2 ∨ a < -1 := by
  rcases h₁ with ⟨x₁, x₂, h₁₂, h₂⟩
  rw [h₀ x₁, h₀ x₂] at h₂
  have eq1 : x₁ ^ 3 + (a + 1) * x₁ ^ 2 + (a + 1) * x₁ + a = x₂ ^ 3 + (a + 1) * x₂ ^ 2 + (a + 1) * x₂ + a := by linarith [h₂]
  have eq2 : x₁ ^ 3 + (a + 1) * x₁ ^ 2 + (a + 1) * x₁ = x₂ ^ 3 + (a + 1) * x₂ ^ 2 + (a + 1) * x₂ := by linarith [eq1]
  have eq3 : x₁ ^ 3 - x₂ ^ 3 + (a + 1) * (x₁ ^ 2 - x₂ ^ 2) + (a + 1) * (x₁ - x₂) = 0 := by linarith [eq2]
  have eq4 : (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a + 1) * (x₁ + x₂) + (a + 1)) = 0 := by
    nlinarith 
  cases (mul_eq_zero.mp eq4) with
  | inl h =>
    exfalso 
    have h3 : x₁ = x₂ := by linarith 
    contradiction
  | inr h =>
    have h3 : (a + 1) * (a - 2) > 0 := by
      nlinarith [sq_pos_of_ne_zero (show x₁ - x₂ ≠ 0 by
        intro h'
        apply h₁₂
        linarith
      ), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ + 2), sq_nonneg (a + 1), sq_nonneg (a - 2)]
    by_cases h4 : a + 1 > 0
    · -- Then a - 2 > 0
      have h5 : a - 2 > 0 := by
        nlinarith 
      left 
      linarith 
    · 
      have h4 : a + 1 < 0 := by 
        by_contra h
        push_neg at h 
        have : a + 1 = 0 := by 
          nlinarith 
        have h5 : a = -1 := by linarith
        rw [h5] at h3 
        nlinarith 
      have h4' : a - 2 < 0 := by 
        nlinarith 
      right
      nlinarith