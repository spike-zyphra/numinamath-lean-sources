import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_70113 (f : ℝ → ℝ) (hf : f = λ x => 2*x^2 + 4*x + 3) :
    IsLeast (range f) (f (-1)) ∧ ∀ x, f x ≥ f (-1) := by
  have h1 : ∀ x, f x = 2 * x^2 + 4 * x + 3 := by
    intro x
    rw [hf]

  have h2 : f (-1) = 1 := by
    rw [h1]
    norm_num
  
  have h3 : ∀ x, f x ≥ f (-1) := by 
    intro x
    rw [h1 x, h2]
    have h4 : 2 * x^2 + 4 * x + 3 ≥ 1 := by 
      nlinarith [sq_nonneg (x + 1)]
    linarith

  have h4 : IsLeast (range f) (f (-1)) := by
    constructor
    · -- show that f (-1) is in the range of f, which is trivial
      simpa using by norm_num
    · -- show that f (-1) is the smallest in the range of f
      intro y
      rintro ⟨x, hx⟩
      have : f x ≥ f (-1) := h3 x
      linarith [this, hx]

  constructor
  · exact h4
  · exact h3