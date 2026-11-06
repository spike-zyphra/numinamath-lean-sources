import Mathlib

theorem algebra_183226 {a : ℝ} (ha : ∃ x1 x2, x1 ≠ x2 ∧ 2*x1^2-2016*(x1-2016+a)-1=a^2 ∧ 2*x2^2-2016*(x2-2016+a)-1=a^2 ∧ x1<a ∧ a<x2) :
    2015 < a ∧ a < 2017 := by
  rcases ha with ⟨x₁, x₂, h12, h₁, h₂, h₃, h₄⟩
  have h3 : 2 * x₁^2 - 2016*(x₁ - 2016 + a) - 1 - a^2 = 0 := by linarith
  have h4 : 2 * x₂^2 - 2016*(x₂ - 2016 + a) - 1 - a^2 = 0 := by linarith
  have h5 : (x₁ - x₂) * (2 * (x₁ + x₂) - 2016) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case where x₁ - x₂ = 0
    exfalso
    exact h12 (by linarith)
  · -- Case where 2 * (x₁ + x₂) - 2016 = 0
    have h7' : x₁ + x₂ = 1008 := by linarith
    have h7'' : x₁ * x₂ = (2016^2 - 2016 * a - 1 - a^2) / 2 := by
      nlinarith [sq_pos_of_ne_zero (show x₁ - x₂ ≠ 0 by intro h; apply h12; linarith), sq_nonneg (x₁ - x₂)]
    have h8 : (a - x₁) * (a - x₂) < 0 := by
      have h7 : x₁ < a := by linarith
      have h8 : a < x₂ := by linarith
      have h9 : a - x₁ > 0 := by linarith
      have h10 : a - x₂ < 0 := by linarith
      exact mul_neg_of_pos_of_neg h9 h10
    have h9 : a^2 - 4032 * a + 2016^2 - 1 < 0 := by
      nlinarith [h8, h7', h7'']
    constructor
    · -- Show 2015 < a
      nlinarith
    · -- Show a < 2017
      nlinarith