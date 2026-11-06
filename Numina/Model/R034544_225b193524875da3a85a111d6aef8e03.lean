import Mathlib
open Real

theorem algebra_611304 (x:ℝ) (h: abs (x-1) = abs (x-2) + abs (x-3)) : (x=2) ∨ (x=4) := by
  by_cases h1 : x ≥ 3
  · -- x ≥ 3
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
    right
    linarith
  · -- x < 3
    by_cases h2 : x ≥ 2
    · -- 2 ≤ x < 3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h
      left
      linarith
    · -- x < 2
      by_cases h3 : x ≥ 1
      · -- 1 ≤ x < 2
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        exfalso
        linarith
      · -- x < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        exfalso
        linarith