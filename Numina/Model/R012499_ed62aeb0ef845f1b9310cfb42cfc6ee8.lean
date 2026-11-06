import Mathlib

open Real
open scoped BigOperators

theorem inequalities_598941 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) ≥ 1 := by

  have h1 : 0 < 3 * a - b + c := by nlinarith
  have h2 : 0 < 3 * b - c + a := by nlinarith
  have h3 : 0 < 3 * c - a + b := by nlinarith

  have h4 : a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) - 1 ≥ 0 := by
    have h5 : a / (3 * a - b + c) + b / (3 * b - c + a) + c / (3 * c - a + b) - 1 =
        (a * (3 * b - c + a) * (3 * c - a + b) +
         b * (3 * a - b + c) * (3 * c - a + b) +
         c * (3 * a - b + c) * (3 * b - c + a) - (3 * a - b + c) * (3 * b - c + a) * (3 * c - a + b)) / ((3 * a - b + c) * (3 * b - c + a) * (3 * c - a + b)) := by
        field_simp
        ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)]
    positivity

  nlinarith [h4]