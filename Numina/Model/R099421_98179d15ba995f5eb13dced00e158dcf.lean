import Mathlib

open Real

theorem algebra_115772 {a b c : ℝ}
    (ha : a = sqrt (1 + 3 + 5 + 7 + 9 + 11) - sqrt (1 + 3 + 5 + 7 + 9))
    (hb : b = sqrt (∑ i in Finset.range 2015, (2 * i + 1)))
    (hc : c = sqrt (∑ i in Finset.range 2014, (2 * i + 1))) :
    a ^ 2015 = 1 ∧ (b - c) ^ 2015 = 1 ∧ (b + c) ^ (a - 1) = 1 := by

  have ha1 : a = 1 := by
    rw [ha]
    have h1 : sqrt (1 + 3 + 5 + 7 + 9 + (11 : ℝ)) = 6 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (1 + 3 + 5 + 7 + (9 : ℝ)) = 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num

  have hb1 : b = 2015 := by
    rw [hb]
    have h4 : (∑ i in Finset.range 2015, (2 * (i : ℝ) + 1)) = (2015 : ℝ) ^ 2 := by
      norm_num [Finset.sum_range_succ]
    rw [h4]
    have h5 : sqrt ((2015 : ℝ) ^ 2) = (2015 : ℝ) := by
      rw [Real.sqrt_sq]
      all_goals norm_num
    rw [h5]

  have hc1 : c = 2014 := by
    rw [hc]
    have h5 : (∑ i in Finset.range 2014, (2 * (i : ℝ) + 1)) = (2014 : ℝ) ^ 2 := by
      norm_num [Finset.sum_range_succ]
    rw [h5]
    have h6 : sqrt ((2014 : ℝ) ^ 2) = (2014 : ℝ) := by
      rw [Real.sqrt_sq]
      all_goals norm_num
    rw [h6]

  constructor
  · -- Show a^2015 = 1
    rw [ha1]
    norm_num

  constructor
  · -- Show (b - c)^2015 = 1
    rw [hb1, hc1]
    norm_num

  · -- Show (b + c)^(a - 1) = 1
    rw [hb1, hc1, ha1]
    norm_num