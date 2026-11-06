import Mathlib

theorem algebra_2161 (a b : ℝ) (ha : |a| = 3) (hb : |b| = 5) :
|(|a + b| -  |a - b|)| = 6 := by 
  cases' eq_or_eq_neg_of_abs_eq ha with ha1 ha2
  · -- Case $a = 3$
    cases' eq_or_eq_neg_of_abs_eq hb with hb1 hb2
    · -- Case $b = 5$
      rw [ha1, hb1]
      norm_num [abs_of_nonneg, abs_of_nonpos]
      all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Case $b = -5$
      rw [ha1, hb2]
      norm_num [abs_of_nonneg, abs_of_nonpos]
      all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Case $a = -3$
    cases' eq_or_eq_neg_of_abs_eq hb with hb1 hb2
    · -- Case $b = 5$
      rw [ha2, hb1]
      norm_num [abs_of_nonneg, abs_of_nonpos]
      all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Case $b = -5$
      rw [ha2, hb2]
      norm_num [abs_of_nonneg, abs_of_nonpos]
      all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
  all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
  all_goals norm_num [abs_of_nonneg, abs_of_nonpos]