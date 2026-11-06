import Mathlib

theorem algebra_175199 (x : ℝ) : |2 * x + 1| + |2 * x - 5| = 6 ↔
    x ∈ Set.Icc (-1 / 2) (5 / 2) := by
  simp only [Set.mem_Icc]
  constructor
  · -- Forward implication: if |2x+1| + |2x-5| = 6, then x ∈ [-1/2, 5/2]
    intro h
    have h1 : x ≥ -1 / 2 := by
      by_cases h2 : x < -1 / 2
      · -- Case 1: x < -1/2
        rw [abs_of_neg (by linarith : 2 * x + 1 < 0), abs_of_neg (by linarith : 2 * x - 5 < 0)] at h
        linarith
      linarith
    have h2 : x ≤ 5 / 2 := by
      by_cases h3 : x > 5 / 2
      · -- Case 3: x >5/2
        rw [abs_of_pos (by linarith : 2 * x + 1 > 0), abs_of_pos (by linarith : 2 * x - 5 > 0)] at h
        linarith
      linarith
    constructor
    · -- x ≥ -1/2
      linarith
    · -- x ≤5/2
      linarith
  · -- Backward implication: if x ∈ [-1/2,5/2], then |2x+1| + |2x-5| =6
    rintro ⟨h1, h2⟩
    have h3 : 2 * x + 1 ≥ 0 := by
      linarith
    have h4 : 2 * x - 5 ≤ 0 := by
      linarith
    rw [abs_of_nonneg h3, abs_of_nonpos h4]
    linarith