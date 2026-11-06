import Mathlib

open Real Set

/- The condition that $x$ should satisfy when it does not meet the inequality $\left| |x+2|-|x-1| \right|>2$ is ___          ___. -/
theorem inequalities_508 (x : ℝ) :
    abs (abs (x + 2) - abs (x - 1)) ≤ 2 ↔ -1.5 ≤ x ∧ x ≤ 0.5 := by
  constructor
  · -- Assume abs (abs (x + 2) - abs (x - 1)) ≤ 2, prove -1.5 ≤ x ∧ x ≤ 0.5
    intro h
    have h1 : -2 ≤ abs (x + 2) - abs (x - 1) := by
      linarith [abs_le.mp h]
    have h2 : abs (x + 2) - abs (x - 1) ≤ 2 := by
      linarith [abs_le.mp h]
    by_cases h3 : x < -2
    · -- Case x < -2
      rw [abs_of_neg (show x + 2 < 0 by linarith), abs_of_neg (show x - 1 < 0 by linarith)] at h1 h2
      nlinarith
    by_cases h4 : x ≤ 1
    · -- Case -2 ≤ x ≤ 1
      rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show x - 1 ≤ 0 by linarith)] at h1 h2
      constructor
      · -- Proving -1.5 ≤ x
        norm_num at h1 ⊢
        linarith
      · -- Proving x ≤ 0.5
        norm_num at h2 ⊢
        linarith
    · -- Case x > 1
      rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show x - 1 ≥ 0 by linarith)] at h1 h2
      norm_num at h2
      all_goals linarith
  · -- Assume -1.5 ≤ x ∧ x ≤ 0.5, prove abs (abs (x + 2) - abs (x - 1)) ≤ 2
    rintro ⟨h1, h2⟩
    have h3 : -2 ≤ x := by
      norm_num at h1 ⊢
      linarith
    have h4 : x ≤ 1 := by
      norm_num at h2 ⊢
      linarith
    have h5 : x + 2 ≥ 0 := by linarith
    have h6 : x - 1 ≤ 0 := by linarith
    have h7 : abs (x + 2) = x + 2 := by
      rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith)]
    have h8 : abs (x - 1) = 1 - x := by
      rw [abs_of_nonpos (show x - 1 ≤ 0 by linarith)]
      all_goals linarith
    have h9 : abs (x + 2) - abs (x - 1) = 2 * x + 1 := by
      rw [h7, h8]
      all_goals linarith
    rw [h9]
    have h10 : abs (2 * x + 1) ≤ 2 := by
      rw [abs_le]
      constructor
      · -- Proving -2 ≤ 2 * x + 1
        norm_num at h1 ⊢
        linarith
      · -- Proving 2 * x + 1 ≤ 2
        norm_num at h2 ⊢
        linarith
    linarith [h10]