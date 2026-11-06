import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_172913 {A B : Set ℝ}
  (hA : A = {x | abs (x + 1 / 2) ≥ 3 / 2})
  (hB : B = {x | x ^ 2 + x < 6}) :
  A ∩ B = {x | -3 < x ∧ x ≤ -2 ∨ 1 ≤ x ∧ x < 2} := by
  ext x
  simp [hA, hB]
  constructor
  · -- Proof of A ∩ B ⊆ {x | -3 < x ∧ x ≤ -2 ∨ 1 ≤ x ∧ x < 2}
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : x ≥ 1 ∨ x ≤ -2 := by
      by_contra h
      push_neg at h
      have h4 : abs (x + 1 / 2) < 3 / 2 := by
        rw [abs_lt]
        constructor
        · linarith
        · linarith
      linarith
    have h4 : -3 < x := by nlinarith
    have h5 : x < 2 := by nlinarith
    rcases h3 with (h3 | h3)
    · -- x ≥ 1
      right
      constructor
      · linarith
      · linarith
    · -- x ≤ -2
      left
      constructor
      · linarith
      · linarith
  · -- Proof of {x | -3 < x ∧ x ≤ -2 ∨ 1 ≤ x ∧ x < 2} ⊆ A ∩ B
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · -- Case -3 < x ∧ x ≤ -2
      constructor
      · -- Show abs (x + 1 / 2) ≥ 3 / 2
        have h3 : abs (x + 1 / 2) ≥ 3 / 2 := by
          have h4 : x + 1 / 2 ≤ -3 / 2 := by linarith
          rw [abs_of_nonpos (by linarith : x + 1 / 2 ≤ 0)]
          linarith
        linarith
      · -- Show x ^ 2 + x < 6
        nlinarith
    · -- Case 1 ≤ x ∧ x < 2
      constructor
      · -- Show abs (x + 1 / 2) ≥ 3 / 2
        have h3 : abs (x + 1 / 2) ≥ 3 / 2 := by
          have h4 : x + 1 / 2 ≥ 3 / 2 := by linarith
          rw [abs_of_nonneg (by linarith : x + 1 / 2 ≥ 0)]
          linarith
        linarith
      · -- Show x ^ 2 + x < 6
        nlinarith