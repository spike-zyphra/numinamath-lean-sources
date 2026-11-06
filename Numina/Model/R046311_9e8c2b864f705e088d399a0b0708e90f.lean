import Mathlib

open Real
open scoped BigOperators

theorem inequalities_215236 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hle : a ≤ b ∧ b ≤ c) (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  (a + b + c)^2 / (b * c) ∈  Set.Ioc 4 9 := by
  have h1 : (a + b + c) ^ 2 / (b * c) > 4 := by
    have h2 : b * c > 0 := by
      apply mul_pos
      all_goals linarith
    have h3 : (a + b + c) ^ 2 > 4 * (b * c) := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
          hle.1, hle.2, 
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c)]
    have h4 : (a + b + c) ^ 2 / (b * c) > 4 := by
      apply (lt_div_iff' (by positivity)).mpr
      linarith
    linarith
  have h2 : (a + b + c) ^ 2 / (b * c) ≤ 9 := by
    have h3 : b * c > 0 := by
      apply mul_pos
      all_goals linarith
    have h4 : (a + b + c) ^ 2 ≤ 9 * (b * c) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
              hle.1, hle.2]
    have h5 : (a + b + c) ^ 2 / (b * c) ≤ 9 := by
      apply (div_le_iff' (by positivity)).mpr
      linarith
    linarith
  constructor
  · -- Show that (a + b + c) ^ 2 / (b * c) > 4
    linarith
  · -- Show that (a + b + c) ^ 2 / (b * c) ≤ 9
    linarith