import Mathlib

theorem inequalities_96779 (x : ℝ) :
    1 ≤ abs (x - 2) ∧ abs (x - 2) ≤ 7 ↔
    (x ≤ 1 ∧ x ≥ -5) ∨ (x ≥ 3 ∧ x ≤ 9) := by
  constructor
  · -- Assume 1 ≤ abs (x - 2) ∧ abs (x - 2) ≤ 7, prove (x ≤ 1 ∧ x ≥ -5) ∨ (x ≥ 3 ∧ x ≤ 9)
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : x - 2 ≥ 0
    · -- Case where |x - 2| = x - 2
      have habs1 : abs (x - 2) = x - 2 := abs_of_nonneg h3
      have h4 : x ≥ 3 := by linarith [h1, habs1]
      have h5 : x ≤ 9 := by linarith [h2, habs1]
      right
      exact ⟨h4, h5⟩
    · -- Case where |x - 2| = -(x - 2) = 2 - x
      have habs2 : abs (x - 2) = -(x - 2) := abs_of_neg (lt_of_not_ge h3)
      have h6 : x ≤ 1 := by linarith [h1, habs2]
      have h7 : x ≥ -5 := by linarith [h2, habs2]
      left
      exact ⟨h6, h7⟩
  · -- Assume (x ≤ 1 ∧ x ≥ -5) ∨ (x ≥ 3 ∧ x ≤ 9), prove 1 ≤ abs (x - 2) ∧ abs (x - 2) ≤ 7
    intro h
    rcases h with (h1 | h2)
    · -- First disjunction: x ≤ 1 ∧ x ≥ -5
      rcases h1 with ⟨h11, h12⟩
      have h4 : x - 2 ≤ -1 := by linarith
      have h5 : abs (x - 2) = -(x - 2) := abs_of_nonpos (by linarith)
      constructor
      · -- Show 1 ≤ abs (x - 2)
        linarith [h5, h11, h12]
      · -- Show abs (x - 2) ≤ 7
        linarith [h5, h11, h12]
    · -- Second disjunction: x ≥ 3 ∧ x ≤ 9
      rcases h2 with ⟨h21, h22⟩
      have h4 : x - 2 ≥ 1 := by linarith
      have h5 : abs (x - 2) = x - 2 := abs_of_nonneg (show x - 2 ≥ 0 by linarith)
      constructor
      · -- Show 1 ≤ abs (x - 2)
        linarith [h5, h21, h22]
      · -- Show abs (x - 2) ≤ 7
        linarith [h5, h21, h22]