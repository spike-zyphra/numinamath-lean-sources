import Mathlib

open Real Set

/- Given $\frac{5-3x}{3}+1\geqslant \frac{2x+3}{5}$, then the maximum value of $\left| x-2 \right|-\left| x+4 \right|$ is ___          ___ , and the minimum value is ___          ___. -/
theorem inequalities_1087 (x : ℝ) (hx : (5 - 3 * x) / 3 + 1 ≥ (2 * x + 3) / 5) :
    |x - 2| - |x + 4| ≤ 6 ∧ |x - 2| - |x + 4| ≥ -104 / 21 := by

  -- Solving the inequality to get the bound on x
  have h1 : x ≤ 31 / 21 := by
    linarith
  -- |x - 2| = 2 - x since x ≤ 2 (as 31/21 < 2)
  have h3 : x ≤ (2 : ℝ) := by
    linarith
  have h4 : |x - 2| = 2 - x := by
    rw [abs_of_nonpos]
    linarith
    all_goals
      linarith

  constructor
  · -- Prove that |x - 2| - |x + 4| ≤ 6
    by_cases h5 : x + 4 ≥ 0
    · -- Case x + 4 ≥ 0
      have h6 : |x + 4| = x + 4 := by
        rw [abs_of_nonneg h5]
      rw [h4, h6]
      -- Simplify to show inequality
      nlinarith [h5, h1]
    · -- Case x + 4 < 0
      have h6 : |x + 4| = -(x + 4) := by
        rw [abs_of_neg (lt_of_not_ge h5)]
      rw [h4, h6]
      -- Use the maximum value here
      linarith [sq_nonneg (x), sq_nonneg (x + 4)]
  · -- Prove that |x - 2| - |x + 4| ≥ -104/21
    by_cases h5 : x + 4 ≥ 0
    · -- Case x + 4 ≥ 0
      have h6 : |x + 4| = x + 4 := by
        rw [abs_of_nonneg h5]
      rw [h4, h6]
      -- Use the bound; it's a linarith problem
      nlinarith [h5, h1]
    · -- Case x + 4 < 0
      have h6 : |x + 4| = -(x + 4) := by
        rw [abs_of_neg (lt_of_not_ge h5)]
      rw [h4, h6]
      -- Use the minimum value here
      linarith [sq_nonneg (x), sq_nonneg (x + 4), h1]