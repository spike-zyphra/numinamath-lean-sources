import Mathlib

theorem algebra_171935 (sqr rbb : ℕ → ℕ)
    (h₀ : sqr 0 = 1) (h₁ : rbb 0 = 1)
    (h₂ : ∀ k, sqr (k + 1) = 2 * sqr k + 2019)
    (h₃ : ∀ k, rbb (k + 1) = 4 * rbb k - 2) :
    IsLeast {y | y > 0 ∧ rbb y > sqr y} 13 := by 
  constructor
  · -- Show 13 is in the set
    constructor
    · -- Show 13 > 0
      norm_num 
    · -- Show rbb 13 > sqr 13
      norm_num [h₀, h₁, h₂, h₃]
  · -- Show no smaller element is in the set
    intro y hy
    rcases hy with ⟨hy1, hy2⟩
    by_contra h
    push_neg at h 
    have h4 : y < 13 := by linarith 
    interval_cases y <;> norm_num [h₀, h₁, h₂, h₃] at hy2 ⊢