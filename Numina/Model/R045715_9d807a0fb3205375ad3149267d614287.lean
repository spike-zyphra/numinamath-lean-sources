import Mathlib

open Real
open scoped BigOperators

theorem inequalities_32195 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a^2 + b^2 > 5 * c^2) :
  min (min a b) c = c := by
  by_cases h4 : a ≤ b
  · -- Assume a ≤ b, then min a b = a
    have h5 : min a b = a := by apply min_eq_left; linarith
    rw [h5]
    by_cases h5 : c ≤ a
    · -- Assume c ≤ a, then min a c = c
      have h6 : min a c = c := by apply min_eq_right; linarith
      rw [h6]
      all_goals linarith
    · -- Assume ¬(c ≤ a)
      have h6 : a < c := by linarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * c), sq_nonneg (a - c), sq_nonneg (b - c)]
  · -- Assume b < a, then min a b = b
    have h5 : min a b = b := by apply min_eq_right; linarith
    rw [h5]
    by_cases h5 : c ≤ b
    · -- Assume c ≤ b, then min b c = c
      have h6 : min b c = c := by apply min_eq_right; linarith
      rw [h6]
      all_goals linarith
    · -- Assume ¬(c ≤ b)
      have h6 : b < c := by linarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * c), sq_nonneg (a - c), sq_nonneg (b - c)]