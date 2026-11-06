import Mathlib

theorem algebra_297315 (a b : ℝ) (ha : 0 < a) (hb : b < 0) :
    {x | abs (x - a) + abs (x - b) = a - b} = {x | b ≤ x ∧ x ≤ a} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume abs (x - a) + abs (x - b) = a - b, prove b ≤ x ∧ x ≤ a
    intro h
    by_cases h1 : x ≥ a
    · -- Case x ≥ a
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      constructor
      · linarith
      · linarith
    · -- Case b ≤ x < a
      by_cases h2 : x ≥ b
      · -- Case b ≤ x < a
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
        constructor
        · linarith
        · linarith
      · -- Case x < b
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        constructor
        · linarith
        · linarith
  · -- Assume b ≤ x ∧ x ≤ a, prove abs (x - a) + abs (x - b) = a - b
    rintro ⟨hbl, har⟩
    by_cases h1 : x ≥ a
    · -- Case x = a
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      all_goals linarith
    · -- Case b ≤ x < a
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      all_goals linarith