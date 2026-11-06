import Mathlib

open Real Set

  theorem algebra_2133 :
    { x : ℝ | (3 - abs (x + 1)) ≥ 0 ∧ (abs (x - 1) - 2) > 0} = {x | -4 ≤ x ∧ x < -1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume x in left set, prove right
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : abs (x + 1) ≤ 3 := by linarith
    have h4 : -4 ≤ x := by
      cases abs_le.mp h3 with
      | intro h5 h6 =>
        linarith
    have h7 : abs (x - 1) > 2 := by linarith
    have h8' : x < -1 := by
      cases abs_cases (x - 1) with
      | inl h8 =>
        nlinarith [abs_le.mp h3]
      | inr h8 =>
        nlinarith
    constructor
    · linarith
    · linarith
  · -- Assume right, prove left
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : abs (x + 1) ≤ 3 := by
      rw [abs_le]
      constructor
      · -- Show -3 ≤ x + 1
        linarith
      · -- Show x + 1 ≤ 3
        linarith
    have h4 : abs (x - 1) > 2 := by
      by_cases h5 : x - 1 ≥ 0
      · -- Assume x - 1 ≥ 0
        rw [abs_of_nonneg h5]
        nlinarith
      · -- Assume x - 1 < 0
        rw [abs_of_neg (by linarith)]
        linarith
    constructor
    · -- Show 3 - abs (x + 1) ≥ 0
      linarith [abs_le.mp h3]
    · -- Show abs (x - 1) - 2 > 0
      linarith [h4]