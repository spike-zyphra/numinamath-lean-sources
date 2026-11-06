import Mathlib

theorem algebra_9412 (x : ℝ) :
    abs (x + 3) - abs (x - 2) ≥ 3 ↔ x ∈ Set.Ici 1 := by
  simp only [Set.mem_Ici]
  constructor
  · -- Assume abs (x + 3) - abs (x - 2) ≥ 3, prove x ≥ 1
    intro h
    by_cases h1 : x ≥ 2
    · -- Case 1: x ≥ 2
      rw [abs_of_nonneg (show x + 3 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith)] at h
      linarith
    · -- Case 2: x < 2
      by_cases h2 : x ≥ -3
      · -- Subcase 2a: -3 ≤ x < 2
        rw [abs_of_nonneg (show x + 3 ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)] at h
        linarith
      · -- Case 2b: x < -3
        rw [abs_of_nonpos (show x + 3 ≤ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)] at h
        linarith
  · -- Assume x ≥ 1, prove abs (x + 3) - abs (x - 2) ≥ 3
    intro h
    by_cases h1 : x ≥ 2
    · -- Case 1: x ≥ 2
      rw [abs_of_nonneg (show x + 3 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith)]
      linarith
    · -- Case 2: x < 2
      have h2 : x < 2 := by linarith
      rw [abs_of_nonneg (show x + 3 ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)]
      linarith