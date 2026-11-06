import Mathlib

/- Real numbers $x, y$ satisfy $3\left| x+1 \right|+2\left| y-1 \right|\leqslant 6$, then the maximum value of $2x-3y$ is ___          __ . -/
theorem algebra_11010 :
    IsGreatest {z : ℝ | ∃ x y, z = 2 * x - 3 * y ∧ 3 * abs (x + 1) + 2 * abs (y - 1) ≤ 6} 4 := by 
  constructor
  · -- Show that 4 is attained
    use -1, -2
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show that 4 is an upper bound
    intro z hz
    rcases hz with ⟨x, y, h_eq, h_abs⟩
    by_cases h1 : x + 1 ≥ 0
    · -- Case where x + 1 ≥ 0, so |x + 1| = x + 1
      rw [abs_of_nonneg h1] at h_abs
      by_cases h2 : y - 1 ≥ 0
      · -- Case where y - 1 ≥ 0, so |y - 1| = y - 1
        rw [abs_of_nonneg h2] at h_abs
        linarith
      · -- Case where y - 1 < 0, so |y - 1| = 1 - y
        rw [abs_of_neg (lt_of_not_ge h2)] at h_abs
        linarith
    · -- Case where x + 1 < 0, so |x + 1| = -(x + 1)
      rw [abs_of_neg (lt_of_not_ge h1)] at h_abs
      by_cases h2 : y - 1 ≥ 0
      · -- Case where y - 1 ≥ 0, so |y - 1| = y - 1
        rw [abs_of_nonneg h2] at h_abs
        linarith
      · -- Case where y - 1 < 0, so |y - 1| = 1 - y
        rw [abs_of_neg (lt_of_not_ge h2)] at h_abs
        linarith