import Mathlib

theorem algebra_1965 (x : ℝ) (A B : ℝ) (hA : A = 3 + x) (hB : B = 3 - x)
    (hAB : |A - B| = 8) : |x| = 4 := by
  rw [hA, hB] at hAB
  have h1 : |(3 + x : ℝ) - (3 - x)| = |2 * x| := by
    have h2 : (3 + x : ℝ) - (3 - x) = 2 * x := by
      ring
    rw [h2]
    all_goals norm_num
  rw [h1] at hAB
  cases' eq_or_eq_neg_of_abs_eq hAB with h2 h2
  · -- Case where 2x = 8, so x = 4
    have hx : x = 4 := by
      linarith
    rw [hx]
    all_goals norm_num
  · -- Case where 2x = -8, so x = -4
    have hx : x = -4 := by
      linarith
    rw [hx]
    all_goals norm_num