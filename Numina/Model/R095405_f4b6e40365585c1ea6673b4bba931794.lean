import Mathlib

/- Given that the real number $x$ satisfies $|2x+1|+|2x-5|=6$, then the range of values for $x$ is ___          ___. -/
theorem algebra_12759 (x : ℝ) :
  abs (2 * x + 1) + abs (2 * x - 5) = 6 ↔ x ∈ Set.Icc (-1 / 2) (5 / 2) := by
  simp only [Set.mem_Icc]
  constructor
  · -- Proof of the forward direction: if abs (2 * x + 1) + abs (2 * x - 5) = 6, then x ∈ [-1/2, 5/2]
    intro h
    by_cases h1 : 2 * x + 1 ≥ 0
    · -- Case where 2x+1 ≥ 0: abs (2 * x + 1) = 2x+1
      rw [abs_of_nonneg h1] at h
      by_cases h2 : 2 * x - 5 ≥ 0
      · -- Case where 2x+1 ≥ 0 and 2x-5 ≥ 0: abs (2 * x - 5) = 2x-5
        rw [abs_of_nonneg h2] at h
        constructor
        · -- Show that x ≥ -1/2
          linarith
        · -- Show that x ≤ 5/2
          linarith
      · -- Case where 2x+1 ≥ 0 and 2x-5 < 0: abs (2 * x - 5) = -(2x-5)
        rw [abs_of_neg (lt_of_not_ge h2)] at h
        constructor
        · -- Show that x ≥ -1/2
          linarith
        · -- Show that x ≤ 5/2
          linarith
    · -- Case where 2x+1 < 0: abs (2 * x + 1) = -(2 * x + 1)
      rw [abs_of_neg (lt_of_not_ge h1)] at h
      by_cases h2 : 2 * x - 5 ≥ 0
      · -- Case where 2x+1 < 0 and 2x-5 ≥ 0: abs (2 * x - 5) = 2 * x - 5
        rw [abs_of_nonneg h2] at h
        constructor
        · -- Show that x ≥ -1/2
          linarith
        · -- Show that x ≤ 5/2
          linarith
      · -- Case where 2x+1 < 0 and 2x-5 < 0: abs (2 * x - 5) = -(2 * x - 5)
        rw [abs_of_neg (lt_of_not_ge h2)] at h
        constructor
        · -- Show that x ≥ -1/2
          linarith
        · -- Show that x ≤ 5/2
          linarith
  · -- Proof of the reverse direction: if x ∈ [-1/2, 5/2], then abs (2 * x + 1) + abs (2 * x - 5) = 6
    rintro ⟨h1, h2⟩
    have h3 : 2 * x + 1 ≥ 0 := by linarith
    have h4 : 2 * x - 5 ≤ 0 := by linarith
    rw [abs_of_nonneg h3, abs_of_nonpos h4]
    linarith