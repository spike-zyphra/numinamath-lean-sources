import Mathlib

theorem inequalities_7265 (x : ℝ) :
    abs (x - 3) + abs (x - 6) < 9 ↔ 0 < x ∧ x < 9 := by
  constructor
  · -- Assume abs (x - 3) + abs (x - 6) < 9, prove 0 < x ∧ x < 9
    intro h
    by_cases h1 : x ≥ 6
    · -- Case x ≥ 6
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      constructor
      · linarith 
      · linarith 
    · -- Case 3 ≤ x < 6
      by_cases h2 : x ≥ 3
      · -- Case 3 ≤ x < 6
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h
        constructor
        · nlinarith 
        · nlinarith 
      · -- Case x < 3
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        constructor
        · nlinarith 
        · nlinarith 
  · -- Assume 0 < x ∧ x < 9, prove abs (x - 3) + abs (x - 6) < 9
    rintro ⟨hx1, hx2⟩
    by_cases h1 : x ≥ 6
    · -- Case x ≥ 6
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      nlinarith
    · -- Case 3 ≤ x < 6
      by_cases h2 : x ≥ 3
      · -- Case 3 ≤ x < 6
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        nlinarith
      · -- Case x < 3
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        nlinarith