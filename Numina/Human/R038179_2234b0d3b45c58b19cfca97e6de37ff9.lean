import Mathlib

theorem algebra_171935 (sqr rbb : ℕ → ℕ)
    (h₀ : sqr 0 = 1) (h₁ : rbb 0 = 1)
    (h₂ : ∀ k, sqr (k + 1) = 2 * sqr k + 2019)
    (h₃ : ∀ k, rbb (k + 1) = 4 * rbb k - 2) :
    IsLeast {y | y > 0 ∧ rbb y > sqr y} 13 := by 
  constructor
  · -- first show 13 satisfies the condition
    constructor
    · norm_num 
    · norm_num [h₀, h₁, h₂, h₃]
  · -- then show there is no smaller value
    intro y hy
    rcases hy with ⟨hy1, hy2⟩
    by_contra h
    push_neg at h
    interval_cases y <;> norm_num [h₀, h₁, h₂, h₃] at hy2