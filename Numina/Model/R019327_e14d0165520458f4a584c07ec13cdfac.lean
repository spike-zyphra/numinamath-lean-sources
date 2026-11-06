import Mathlib

open Real
open scoped BigOperators

theorem inequalities_36378 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  |(a / b) + (b / c) + (c / a) - (b / a) - (c / b) - (a / c)| < 1 := by

  have h1 : -1 < (a / b) + (b / c) + (c / a) - (b / a) - (c / b) - (a / c) := by
    have h2 : (a / b) + (b / c) + (c / a) - (b / a) - (c / b) - (a / c) + 1 > 0 := by
      have h3 : (a / b) + (b / c) + (c / a) - (b / a) - (c / b) - (a / c) + 1 =
          ( (a^2 * c + b^2 * a + c^2 * b - b^2 * c - c^2 * a - a^2 * b + a * b * c ) ) / (a * b * c) := by
        field_simp
        ring
      rw [h3] at *
      have h1 : 0 < a * b * c := by
        apply mul_pos
        apply mul_pos
        exact ha
        exact hb
        exact hc
      have h5 : a ^ 2 * c + b ^ 2 * a + c ^ 2 * b - b ^ 2 * c - c ^ 2 * a - a^2 * b + a * b * c > 0 := by
        nlinarith [ mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h'') ]
      have h4 : ( (a^2 * c + b^2 * a + c^2 * b - b^2 * c - c^2 * a - a^2 * b + a * b * c ) ) / (a * b * c) > 0 := by
        apply div_pos
        linarith
        all_goals linarith
      linarith
    linarith

  have h2 : (a / b) + (b / c) + (c / a) - (b / a) - (c / b) - (a / c) < 1 := by
    have h3 : (a / b) + (b / c) + (c / a) - (b / a) - (c / b) - (a / c) - 1 < 0 := by
      have h4 : (a / b) + (b / c) + (c / a) - (b / a) - (c / b) - (a / c) - 1 =
          ( (a^2 * c + b^2 * a + c^2 * b - b^2 * c - c^2 * a - a^2 * b - a * b * c ) ) / (a * b * c) := by
        field_simp
        ring
      rw [h4] at *
      have h1 : 0 < a * b * c := by
        apply mul_pos
        apply mul_pos
        exact ha
        exact hb
        exact hc
      have h5 : a ^ 2 * c + b ^ 2 * a + c ^ 2 * b - b ^ 2 * c - c^2 * a - a^2 * b - a * b * c < 0 := by
        nlinarith [ mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h'') ]
      have h4 : ( (a^2 * c + b^2 * a + c^2 * b - b^2 * c - c^2 * a - a^2 * b - a * b * c ) ) / (a * b * c) < 0 := by
        apply div_neg_of_neg_of_pos
        linarith
        all_goals linarith
      linarith
    linarith

  apply abs_lt.mpr
  constructor
  · linarith [h1]
  · linarith [h2]