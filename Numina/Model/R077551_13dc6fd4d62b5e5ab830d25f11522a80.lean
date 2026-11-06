import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_160499 (f : ℝ → ℝ) (hf : f = λ x => (x - 8) / (x ^ 2 - 7 * x + 12)) :
    {x | x ≠ 3 ∧ x ≠ 4} = {x | x < 3 ∨ x ∈ Ioo 3 4 ∨ x > 4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- First direction: if x ≠ 3 ∧ x ≠ 4, then x < 3 ∨ (3 < x < 4) ∨ x > 4
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : x < 3
    · -- If x < 3, then it's in the first part of the union
      left
      exact h3
    · -- If ¬x < 3, then x ≥ 3
      have h3' : x ≥ 3 := by linarith
      have h4 : x > 3 := by
        by_contra h4
        push_neg at h4
        have h3_eq : x = 3 := by linarith [h4, h3']
        contradiction
      by_cases h5 : x < 4
      · -- If x < 4, then 3 < x < 4
        right
        left
        constructor
        · linarith
        · linarith
      · -- If ¬x < 4, then x ≥ 4
        have h5' : x ≥ 4 := by linarith
        have h6 : x > 4 := by
          by_contra h6
          push_neg at h6
          have h4_eq : x = 4 := by linarith [h6, h5']
          contradiction
        right
        right
        linarith
  · -- Second direction: if x < 3 ∨ (3 < x < 4) ∨ x > 4, then x ≠ 3 ∧ x ≠ 4
    intro h
    rcases h with (h1 | h1 | h1)
    · -- If x < 3
      constructor
      · -- x ≠ 3
        by_contra h2
        have h3 : x = 3 := by linarith
        linarith
      · -- x ≠ 4
        by_contra h2
        have h3 : x = 4 := by linarith
        linarith
    · -- If 3 < x < 4
      constructor
      · -- x ≠ 3
        by_contra h2
        have h3 : x = 3 := by linarith
        nlinarith
      · -- x ≠ 4
        by_contra h2
        have h3 : x = 4 := by linarith
        nlinarith
    · -- If x > 4
      constructor
      · -- x ≠ 3
        by_contra h2
        have h3 : x = 3 := by linarith
        linarith
      · -- x ≠ 4
        by_contra h2
        have h3 : x = 4 := by linarith
        linarith