import Mathlib

open Real Set

theorem inequalities_286564 (x : ℝ) :
    (1 ≤ abs (x - 2) ∧ abs (x - 2) ≤ 7) ↔
    (-5 ≤ x ∧ x ≤ 1) ∨ (3 ≤ x ∧ x ≤ 9) := by
  constructor
  · -- Forward direction: both conditions imply the two intervals
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : x - 2 ≥ 0
    · -- Case 1: x - 2 >= 0, so |x - 2| = x - 2
      have h4 : abs (x - 2) = x - 2 := abs_of_nonneg (show x - 2 ≥ 0 by linarith)
      have h5 : 3 ≤ x := by linarith [h1, h4]
      have h6 : x ≤ 9 := by linarith [h2, h4]
      right
      constructor
      · linarith
      · linarith
    · -- Case 2: x - 2 < 0, so |x - 2| = -(x - 2)
      have h4 : abs (x - 2) = -(x - 2) := abs_of_neg (show x - 2 < 0 by linarith)
      have h7 : x ≤ 1 := by linarith [h1, h4]
      have h8 : x ≥ -5 := by linarith [h2, h4]
      left
      constructor
      · linarith
      · linarith
  · -- Reverse direction: the two intervals imply both conditions
    rintro (h | h)
    · -- Case where $-5 ≤ x ∧ x ≤ 1$
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Proof that $1 ≤ |x - 2|$
        have h3 : abs (x - 2) = -(x - 2) := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        rw [h3]
        linarith
      · -- Proof that $|x - 2| ≤ 7$
        have h3 : abs (x - 2) = -(x - 2) := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        rw [h3]
        linarith
    · -- Case where $3 ≤ x ∧ x ≤ 9$
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Proof that $1 ≤ |x - 2|$
        have h3 : abs (x - 2) = x - 2 := by
          rw [abs_of_nonneg]
          linarith
        rw [h3]
        linarith
      · -- Proof that $|x - 2| ≤ 7$
        have h3 : abs (x - 2) = x - 2 := by
          rw [abs_of_nonneg]
          linarith
        rw [h3]
        linarith