import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_213980 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (habc : a * b * c = 1) :
  1 ≤ 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) := by
    have h1 : 0 < 2 * a + 1 := by 
      nlinarith
    have h2 : 0 < 2 * b + 1 := by 
      nlinarith
    have h3 : 0 < 2 * c + 1 := by 
      nlinarith
    have h4 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1 ≥ 0 := by 
      have h5 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1 =
        ((2 * b + 1) * (2 * c + 1) + (2 * a + 1) * (2 * c + 1) + (2 * a + 1) * (2 * b + 1) - (2 * a + 1) * (2 * b + 1) * (2 * c + 1)) / ((2 * a + 1) * (2 * b + 1) * (2 * c + 1)) := by
        field_simp
        <;> ring
      rw [h5]
      apply div_nonneg
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
        sq_nonneg (a + b + c - 3), sq_nonneg (a * b * c - 1), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      positivity
    linarith