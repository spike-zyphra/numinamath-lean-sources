import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311961 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x ∈ Icc 0 1, |f x| ≤ 1)
  (h₀ : ∀ x, f x = a * x + b) :
  -2 ≤ (a + 1) * (b + 1) ∧ (a + 1) * (b + 1) ≤ 9 / 4 := by

  have h1 : -1 ≤ b := by 
    specialize hf 0 (by norm_num)
    rw [h₀] at hf
    cases' abs_le.mp hf with h3 h4
    linarith

  have h2 : b ≤ 1 := by
    specialize hf 0 (by norm_num)
    rw [h₀] at hf
    cases' abs_le.mp hf with h3 h4
    linarith

  have h3 : -1 ≤ a + b := by
    specialize hf 1 (by norm_num)
    rw [h₀] at hf
    cases' abs_le.mp hf with h4 h5
    linarith

  have h4 : a + b ≤ 1 := by 
    specialize hf 1 (by norm_num)
    rw [h₀] at hf
    cases' abs_le.mp hf with h5 h6
    linarith

  have h5 : -1 ≤ a / 2 + b := by 
    specialize hf (1 / 2) (by norm_num)
    rw [h₀] at hf
    cases' abs_le.mp hf with h6 h7
    linarith

  have h6 : a / 2 + b ≤ 1 := by 
    specialize hf (1 / 2) (by norm_num)
    rw [h₀] at hf
    cases' abs_le.mp hf with h7 h8
    linarith

  constructor
  · -- Prove -2 ≤ (a + 1) * (b + 1)
    nlinarith [sq_nonneg (a + 2), sq_nonneg (b - 1), sq_nonneg (b - a - 2), sq_nonneg (a + 4), sq_nonneg (b + 1)]
  · -- Prove (a + 1) * (b + 1) ≤ 9 / 4
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (b - a), sq_nonneg (b + 1), sq_nonneg (a + 2)]