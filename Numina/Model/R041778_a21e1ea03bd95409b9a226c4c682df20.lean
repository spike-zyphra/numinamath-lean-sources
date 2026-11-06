import Mathlib

open Real
open scoped BigOperators

theorem inequalities_66138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a / (b + c) + b / (c + a) + c / (a + b) < 2 := by

  have h2 : a / (b + c) + b / (c + a) + c / (a + b) - 2 < 0 := by

    have h3 : a / (b + c) + b / (c + a) + c / (a + b) - 2 =
        (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring

    have h4 : a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) < 2 * (b + c) * (c + a) * (a + b) := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), -- (a+b-c)(a+c-b) > 0
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), -- (a+b-c)(b+c-a) > 0
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h'') -- (a+c-b)(b+c-a) > 0
      ]

    have h5 : a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b) < 0 := by linarith

    have h7 : (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) < 0 := by
      apply div_neg_of_neg_of_pos
      linarith
      positivity

    linarith [h3, h7]

  linarith