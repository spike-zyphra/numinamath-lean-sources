import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10507  (f : ℝ → ℝ) (hf : f = λ x => (x^4 - 4 * x^3 + 6 * x^2 - 4 * x + 1) / (x^2 - 4)) :  {x | x^2 - 4 ≠ 0} = {x | x < -2 ∨ x ∈ Ioo (-2) 2 ∨ x > 2 }:= by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_Ioo, and_imp]
  constructor
  · -- Assume h : x^2 - 4 ≠ 0, prove x < -2 ∨ (x > -2 ∧ x < 2) ∨ x > 2
    intro h
    have h1 : x ≠ 2 := by
      by_contra h2
      rw [h2] at h
      norm_num at h
    have h2 : x ≠ -2 := by
      by_contra h3
      rw [h3] at h
      norm_num at h 
    by_cases h3 : x < -2 
    · -- x < -2 
      left 
      assumption 
    · -- x ≥ -2
      have h4 : x > -2 := by
        by_contra h4
        push_neg at h4 
        have : x = -2 := by linarith 
        contradiction 
      by_cases h5 : x < 2 
      · -- x > -2 ∧ x < 2 
        right 
        left 
        constructor <;> linarith 
      · -- x ≥ 2
        have h6 : x > 2 := by
          by_contra h7 
          push_neg at h7 
          have h7 : x = 2 := by 
            nlinarith 
          contradiction 
        right 
        right 
        linarith 
  · -- Assume h : x < -2 ∨ (x > -2 ∧ x < 2) ∨ x > 2, prove x^2 - 4 ≠ 0 
    rintro (h | ⟨h1, h2⟩ | h)
    · -- x < -2 
      nlinarith 
    · -- x > -2 ∧ x < 2 
      nlinarith 
    · -- x > 2 
      nlinarith