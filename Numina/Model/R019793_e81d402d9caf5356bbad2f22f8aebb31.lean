import Mathlib

open Real
open scoped BigOperators

theorem inequalities_71705 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a + b + c = 12) :
  2.875 ≤ a / (b + c - a) + 4 * b / (c + a - b) + 9 * c / (a + b - c) := by
  have hb1 : 0 < b + c - a := by
    linarith
  have hb2 : 0 < c + a - b := by
    linarith
  have hb3 : 0 < a + b - c := by
    linarith
  have h1 : a / (b + c - a) + 4 * b / (c + a - b) + 9 * c / (a + b - c) - 2.875 ≥ 0 := by
    have h3 : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by
      positivity
    have h6 : a / (b + c - a) + 4 * b / (c + a - b) + 9 * c / (a + b - c) - 2.875 =
          ( a * (c + a - b) * (a + b - c) + 4 * b * (b + c - a) * (a + b - c) + 9 * c * (b + c - a) * (c + a - b) - 2.875 * (b + c - a) * (c + a - b) * (a + b - c) ) / ( (b + c - a) * (c + a - b) * (a + b - c) ) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [ mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos hb1 hb2, mul_pos hb1 hb3, mul_pos hb2 hb3, 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg ( (b + c - a) - (c + a - b) ), 
        sq_nonneg ( (b + c - a) - (a + b - c) ), 
        sq_nonneg ( (c + a - b) - (a + b - c) ), 
        mul_pos hb1 hb2, mul_pos hb1 hb3, mul_pos hb2 hb3, 
        h, h', h''
      ]
    all_goals positivity
  linarith