import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_110741 (f : ℝ → ℝ) (hf : f = λ x => abs (x - 1) + abs (2 * x - 1) + abs (3 * x - 1)) :
    range f = {y | y ≥ 1} := by
  ext y
  simp only [hf, Set.mem_range, Set.mem_setOf_eq]
  constructor
  · -- Assume y ∈ range f, need to show y ≥ 1
    intro hy
    rcases hy with ⟨x, hx⟩
    have h1 : abs (x - 1) + abs (2 * x - 1) + abs (3 * x - 1) ≥ 1 := by
      by_cases h1 : x ≥ 1
      · -- x ≥ 1
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      by_cases h2 : x ≥ 1 / 2
      · -- 1 / 2 ≤ x < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        all_goals linarith
      by_cases h3 : x ≥ 1 / 3
      · -- 1 / 3 ≤ x < 1 / 2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        all_goals linarith
      · -- x < 1 / 3
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        all_goals linarith
    linarith [h1, hx]
  · -- Assume y ≥ 1, need to show y ∈ range f
    intro h1
    by_cases h11 : y ≥ 3
    · -- Case where y ≥ 3
      use (y + 3) / 6
      have h41 : y ≥ 3 := h11
      have h42 : (y + 3) / 6 ≥ 1 := by
        linarith
      have h1 : abs ((y + 3) / 6 - 1) = ((y + 3) / 6 - 1) := by
        rw [abs_of_nonneg]
        all_goals nlinarith
      have h2 : abs (2 * ((y + 3) / 6) - 1) = (2 * ((y + 3) / 6) - 1) := by
        rw [abs_of_nonneg]
        all_goals nlinarith
      have h3 : abs (3 * ((y + 3) / 6) - 1) = (3 * ((y + 3) / 6) - 1) := by
        rw [abs_of_nonneg]
        all_goals nlinarith
      rw [h1, h2, h3]
      all_goals linarith
    · -- Case where 1 ≤ y < 3
      have h12 : 1 ≤ y := by linarith
      have h21 : y < 3 := by linarith
      use (y + 1) / 4
      have h31 : 1 / 2 ≤ (y + 1) / 4 := by
        linarith
      have h32 : (y + 1) / 4 < 1 := by
        linarith
      have h4 : abs ((y + 1) / 4 - 1) = 1 - ((y + 1) / 4) := by
        rw [abs_of_nonpos]
        all_goals nlinarith
      have h5 : abs (2 * ((y + 1) / 4) - 1) = (2 * ((y + 1) / 4) - 1) := by
        rw [abs_of_nonneg]
        all_goals nlinarith
      have h6 : abs (3 * ((y + 1) / 4) - 1) = (3 * ((y + 1) / 4) - 1) := by
        rw [abs_of_nonneg]
        all_goals nlinarith
      rw [h4, h5, h6]
      all_goals linarith