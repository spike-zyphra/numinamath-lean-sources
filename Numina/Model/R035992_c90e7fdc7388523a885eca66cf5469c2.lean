import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_274672 (a b c : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x ∈ Icc 0 1, |f x| ≤ 1)
  (h₁ : f = λ x => a * x^2 + b * x + c) :
  |a| + |b| + |c| ≤ 17 := by
  have h2 : -1 ≤ c ∧ c ≤ 1 := by
    have h3 := h₀ 0 (by norm_num)
    simp [h₁] at h3
    constructor
    · linarith [abs_le.mp h3]
    · linarith [abs_le.mp h3]

  have h6 : -1 ≤ a + b + c ∧ a + b + c ≤ 1 := by
    have h7 := h₀ 1 (by norm_num)
    simp [h₁] at h7
    constructor
    · linarith [abs_le.mp h7]
    · linarith [abs_le.mp h7]
  have h8 : -1 ≤ (a / 4) + (b / 2) + c ∧ (a / 4) + (b / 2) + c ≤ 1 := by
    have h9 := h₀ (1 / 2) (by norm_num)
    simp [h₁] at h9
    constructor
    · linarith [abs_le.mp h9]
    · linarith [abs_le.mp h9]
  cases' abs_cases a with ha ha <;> cases' abs_cases b with hb hb <;> cases' abs_cases c with hc hc <;> 
    all_goals
      linarith