import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_10841 {A B : Set ℝ}
  (hA : A = {x | abs (x - 2) ≤ 1}) (hB : B = {x | (x - 5) / (2 - x) > 0}) :
  A ∩ B = {x | 2 < x ∧ x ≤ 3} := by
  ext x
  simp [hA, hB]
  constructor
  · -- Assume x ∈ A ∩ B; prove x ∈ {x | 2 < x ∧ x ≤ 3}
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : 1 ≤ x ∧ x ≤ 3 := by
      constructor
      · 
        linarith [abs_le.mp h1]
      · 
        linarith [abs_le.mp h1]
    have h4 : 2 < x := by
      by_contra h
      push_neg at h
      have : (x - 5) / (2 - x) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Show x - 5 ≤ 0 
          nlinarith
        · -- Show 2 - x ≥ 0 
          nlinarith 
      linarith
    constructor
    · linarith
    · linarith
  · -- Assume x ∈ {x | 2 < x ∧ x ≤ 3}; prove x ∈ A ∩ B
    intro h
    rcases h with ⟨h2, h3⟩
    constructor
    · -- Show |x - 2| ≤ 1 
      have h1 : abs (x - 2) ≤ 1 := by
        rw [abs_of_pos (by linarith)]
        all_goals linarith
      exact h1
    · -- Show (x - 5) / (2 - x) > 0 
      have h4 : (x - 5) / (2 - x) > 0 := by
        apply div_pos_of_neg_of_neg 
        all_goals linarith 
      exact h4