import Mathlib

open Real
open scoped BigOperators

theorem inequalities_9005 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  |(a/b) + (b/c) + (c/a) - (a/c) - (c/b) - (b/a)| < 1 := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : -1 < (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) := by
    have h4 : (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) > -1 := by
      have pos1 : 0 < a * b * c := h1
      have h6 : (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) + 1 > 0 := by
        have pos1 : 0 < a * b * c := h1
        have h7 : (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) + 1 =
            (a^2 * c + b^2 * a + c^2 * b - a^2 * b - c^2 * a - b^2 * c + a * b * c) / (a * b * c) := by
          field_simp
          ring
        rw [h7] at *
        apply div_pos
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
          ]
        all_goals positivity
      linarith
    linarith

  have h3 : (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) < 1 := by
    have h4 : (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) < 1 := by
      have pos1 : 0 < a * b * c := h1
      have h6 : (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) - 1 < 0 := by
        have pos1 : 0 < a * b * c := h1
        have h7 : (a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a) - 1 =
            (a^2 * c + b^2 * a + c^2 * b - a^2 * b - c^2 * a - b^2 * c - a * b * c) / (a * b * c) := by
          field_simp
          ring
        rw [h7] at *
        apply div_neg_of_neg_of_pos
        · nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
          ]
        all_goals positivity
      linarith
    linarith

  have h4 : |(a / b) + (b / c) + (c / a) - (a / c) - (c / b) - (b / a)| < 1 := by
    rw [abs_lt]
    constructor
    · linarith
    · linarith
  exact h4