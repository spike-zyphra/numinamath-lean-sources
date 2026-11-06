import Mathlib

open Real
open scoped BigOperators

theorem inequalities_157694 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  3 ≤ a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
  have h1 : 0 < b + c - a := by linarith
  have h2 : 0 < c + a - b := by linarith
  have h3 : 0 < a + b - c := by linarith
  
  have h4 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3 ≥ 0 := by
    have h5 : (a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3) =
        ( (a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c)) / ((b + c - a) * (c + a - b) * (a + b - c)) ) := by
      field_simp
      ring
    rw [h5]

    -- Now need to show >0
    have h6 : ( (b + c - a) * (c + a - b) * (a + b - c) ) > 0 := by
      positivity

    have h7 : a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)
          ]
    
    apply div_nonneg
    linarith
    positivity
  
  linarith