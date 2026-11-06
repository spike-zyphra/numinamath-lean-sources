import Mathlib

open Finset BigOperators

theorem Algebra_611313 (a b:ℝ ) (hab : a - b ≠ 0) (hf : deriv (λ x:ℝ ↦ x^3+a*x+b) a = deriv (λ x:ℝ ↦ x^3+a*x+b) b) : (λ x:ℝ ↦ x^3+a*x+b) 1 = 1 := by
  have h1 : deriv (λ x:ℝ ↦ x^3+a*x+b) a = 3 * a ^ 2 + a := by
    simp [deriv_pow, deriv_const, deriv_id', mul_comm a, mul_assoc]
    all_goals ring
  have h2 : deriv (λ x:ℝ ↦ x^3+a*x+b) b = 3 * b ^ 2 + a := by
    simp [deriv_pow, deriv_const, deriv_id', mul_comm a, mul_assoc]
    all_goals ring
  rw [h1, h2] at hf
  have h3 : 3 * a ^ 2 = 3 * b ^ 2 := by
    linarith 
  have h4 : a ^ 2 = b ^ 2 := by
    nlinarith 
  have h5 : a = b ∨ a = -b := by 
    have h6 : a ^ 2 - b ^ 2 = 0 := by
      nlinarith
    have h7 : (a - b) * (a + b) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h7) with h8 h9
    · left
      linarith 
    · right 
      linarith 
  cases h5 with
  | inl h5 =>
    -- This contradicts the hypothesis a - b ≠ 0
    have h6 : a - b = 0 := by 
      linarith
    contradiction 
  | inr h5 =>
    -- So a = -b
    -- We need to prove that f(1) = 1
    -- f(1) = 1^3 + a * 1 + b 
    -- = 1 + (-b) * 1 + b 
    -- = 1 - b + b 
    -- = 1
    have h6 : (λ x:ℝ ↦ x^3+a*x+b) 1 = 1 ^ 3 + a * 1 + b := by 
      simp 
    rw [h6] 
    have h7 : a = -b := by linarith 
    rw [h7] 
    ring