import Mathlib

theorem inequalities_117156 (x y : ℝ) (h₁ : abs (x - 1) + abs (x + 2) ≤ 3) (h₂ : abs (y + 1) + abs (y - 2) ≤ 7) :
    x - y ≤ 4 := by
  have h3 : x ≤ 1 := by
    by_cases h : x ≥ 1
    · -- Case 1: x ≥ 1
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h₁
      linarith
    · -- Case 2: x < 1
      by_cases h' : x ≥ -2
      · -- Case 2a: -2 ≤ x < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h₁
        linarith
      · -- Case 2b: x < -2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h₁
        linarith
  have h4 : -2 ≤ x := by
    by_cases h : x ≥ 1
    · -- Case 1: x ≥ 1
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h₁
      linarith
    · -- Case 2: x < 1
      by_cases h' : x ≥ -2
      · -- Case 2a: -2 ≤ x < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h₁
        linarith
      · -- Case 2b: x < -2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h₁
        linarith
  have h5 : y ≤ 4 := by
    by_cases h : y ≥ 2
    · -- Case 1: y ≥ 2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h₂
      linarith
    · -- Case 2: y < 2
      by_cases h' : y ≥ -1
      · -- Case 2a: -1 ≤ y < 2
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h₂
        linarith
      · -- Case 2b: y < -1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h₂
        linarith
  have h6 : -3 ≤ y := by
    by_cases h : y ≥ 2
    · -- Case 1: y ≥ 2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h₂
      linarith
    · -- Case 2: y < 2
      by_cases h' : y ≥ -1
      · -- Case 2a: -1 ≤ y < 2
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h₂
        linarith
      · -- Case 2b: y < -1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h₂
        linarith
  linarith