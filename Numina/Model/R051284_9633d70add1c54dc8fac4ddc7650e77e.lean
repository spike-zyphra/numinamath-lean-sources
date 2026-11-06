import Mathlib

open Real Set

theorem inequalities_218114 (x : ℝ) :
    abs (x + 1) + abs x < 2 ↔ -3 / 2 < x ∧ x < 1 / 2 := by
  constructor
  · -- Forward implication
    intro h
    constructor
    · -- Proving -3/2 < x
      by_cases h1 : x ≥ 0
      · -- Case x ≥ 0
        have hx1 : abs (x + 1) = x + 1 := abs_of_nonneg (show x + 1 ≥ 0 by linarith)
        have hx2 : abs x = x := abs_of_nonneg (show x ≥ 0 by linarith)
        rw [hx1, hx2] at h
        linarith
      · -- Case x < 0
        by_cases h2 : x + 1 ≥ 0
        · -- Case -1 ≤ x < 0
          have hx3 : abs (x + 1) = x + 1 := abs_of_nonneg (show x + 1 ≥ 0 by linarith)
          have hx4 : abs x = -x := abs_of_nonpos (show x ≤ 0 by linarith)
          rw [hx3, hx4] at h
          linarith
        · -- Case x < -1
          have hx5 : abs (x + 1) = -(x + 1) := abs_of_nonpos (show x + 1 ≤ 0 by linarith)
          have hx6 : abs x = -x := abs_of_nonpos (show x ≤ 0 by linarith)
          rw [hx5, hx6] at h
          linarith
    · -- Proving x < 1/2
      by_cases h1 : x ≥ 0
      · -- Case x ≥ 0
        have hx1 : abs (x + 1) = x + 1 := abs_of_nonneg (show x + 1 ≥ 0 by linarith)
        have hx2 : abs x = x := abs_of_nonneg (show x ≥ 0 by linarith)
        rw [hx1, hx2] at h
        linarith
      · -- Case x < 0
        by_cases h2 : x + 1 ≥ 0
        · -- Case -1 ≤ x < 0
          have hx3 : abs (x + 1) = x + 1 := abs_of_nonneg (show x + 1 ≥ 0 by linarith)
          have hx4 : abs x = -x := abs_of_nonpos (show x ≤ 0 by linarith)
          rw [hx3, hx4] at h
          linarith
        · -- Case x < -1
          have hx5 : abs (x + 1) = -(x + 1) := abs_of_nonpos (show x + 1 ≤ 0 by linarith)
          have hx6 : abs x = -x := abs_of_nonpos (show x ≤ 0 by linarith)
          rw [hx5, hx6] at h
          linarith
  · -- Backward implication
    rintro ⟨h1, h2⟩
    by_cases h3 : x ≥ 0
    · -- Case x ≥ 0
      have hx1 : abs (x + 1) = x + 1 := abs_of_nonneg (show x + 1 ≥ 0 by linarith)
      have hx2 : abs x = x := abs_of_nonneg (show x ≥ 0 by linarith)
      rw [hx1, hx2]
      linarith
    · -- Case x < 0
      by_cases h4 : x + 1 ≥ 0
      · -- Case -1 ≤ x < 0
        have hx3 : abs (x + 1) = x + 1 := abs_of_nonneg (show x + 1 ≥ 0 by linarith)
        have hx4 : abs x = -x := abs_of_nonpos (show x ≤ 0 by linarith)
        rw [hx3, hx4]
        linarith
      · -- Case x < -1
        have hx5 : abs (x + 1) = -(x + 1) := abs_of_nonpos (show x + 1 ≤ 0 by linarith)
        have hx6 : abs x = -x := abs_of_nonpos (show x ≤ 0 by linarith)
        rw [hx5, hx6]
        linarith