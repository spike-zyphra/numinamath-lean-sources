import Mathlib

theorem inequalities_297611 (a : ℝ) :
    (∀ x : ℝ, abs (x - 2) + abs (x - 1) ≥ a) ↔ a ≤ 1 := by
  constructor
  · -- Assume the inequality holds for all x, we need to prove a ≤ 1.
    intro h
    have h1 := h 1.5
    norm_num [abs] at h1
    linarith
  · -- Assume a ≤ 1, we need to prove the inequality holds for all x.
    intro ha x
    have h2 : abs (x - 2) + abs (x - 1) ≥ 1 := by 
      by_cases h1 : x ≥ 2
      · -- Case 1: x ≥ 2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      by_cases h2 : x ≥ 1
      · -- Case 2: 1 ≤ x < 2
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Case 3: x < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    linarith