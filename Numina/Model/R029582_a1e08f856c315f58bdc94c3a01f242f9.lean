import Mathlib

open Real
open scoped BigOperators

theorem inequalities_313182 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  23/16 < a/(a + b) + b/(b + c) + c/(c + a) ∧
  a/(a + b) + b/(b + c) + c/(c + a) < 25/16 := by
  constructor
  · -- Prove the lower bound
    have pos1 : 0 < a + b := by linarith
    have pos2 : 0 < b + c := by linarith
    have pos3 : 0 < c + a := by linarith
    have h1 : 23 / 16 < a / (a + b) + b / (b + c) + c / (c + a) := by
      have pos1 : 0 < a + b := by linarith
      have pos2 : 0 < b + c := by linarith
      have pos3 : 0 < c + a := by linarith
      have h1' : a / (a + b) + b / (b + c) + c / (c + a) - 23 / 16 > 0 := by
        have h_pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
        have eq1 : a / (a + b) + b / (b + c) + c / (c + a) - 23 / 16 =
          ( (a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c) - 23 / 16 * (a + b) * (b + c) * (c + a) ) / ( (a + b) * (b + c) * (c + a) ) ) := by 
          field_simp
          ring 
        rw [eq1] at *
        apply div_pos
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          mul_pos ha (show 0 < b * c by nlinarith), 
          mul_pos hb (show 0 < a * c by nlinarith), 
          mul_pos hc (show 0 < a * b by nlinarith)
        ]
        all_goals 
          positivity
      linarith 
    linarith 
  · -- Prove the upper bound
    have pos1 : 0 < a + b := by linarith
    have pos2 : 0 < b + c := by linarith
    have pos3 : 0 < c + a := by linarith
    have h2 : a / (a + b) + b / (b + c) + c / (c + a) < 25 / 16 := by
      have pos1 : 0 < a + b := by linarith
      have pos2 : 0 < b + c := by linarith
      have pos3 : 0 < c + a := by linarith
      have h1' : a / (a + b) + b / (b + c) + c / (c + a) - 25 / 16 < 0 := by
        have h_pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
        have eq1 : a / (a + b) + b / (b + c) + c / (c + a) - 25 / 16 =
          ( (a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c) - 25 / 16 * (a + b) * (b + c) * (c + a) ) / ( (a + b) * (b + c) * (c + a) ) ) := by 
          field_simp
          ring 
        rw [eq1] at *
        apply div_neg_of_neg_of_pos
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          mul_pos ha (show 0 < b * c by nlinarith), 
          mul_pos hb (show 0 < a * c by nlinarith), 
          mul_pos hc (show 0 < a * b by nlinarith)
        ]
        all_goals 
          positivity
      linarith 
    linarith