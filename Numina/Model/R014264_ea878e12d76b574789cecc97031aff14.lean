import Mathlib

open Real Set

theorem inequalities_596989 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : ℝ) (hS : S = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) :
    1 < S ∧ S < 2 := by

  have h1 : 1 < S := by
    rw [hS]
    have h1 : 0 < a := ha
    have h2 : 0 < b := hb
    have h3 : 0 < c := hc
    have h4 : 0 < d := hd
    have h5 : 0 < a + b + c := by linarith
    have h6 : 0 < a + b + d := by linarith
    have h7 : 0 < b + c + d := by linarith
    have h8 : 0 < a + c + d := by linarith
    have h9 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
      have pos1 : 0 < (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) := by positivity
      have h10 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 > 0 := by
        have h11 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 =
            ( a * (a + b + c) * (b + c + d) * (a + c + d) + b * (a + b + d) * (b + c + d) * (a + c + d) + c * (a + b + d) * (a + b + c) * (a + c + d) + d * (a + b + d) * (a + b + c) * (b + c + d) - (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) ) / ( (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) ) := by
          field_simp
          ring
        rw [h11]
        apply div_pos
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
            mul_pos hb hc, mul_pos hb hd, 
            mul_pos hc hd, 
            mul_pos (show 0 < a + b + c from by linarith) (show 0 < a + b + d from by linarith), 
            mul_pos (show 0 < a + b + c from by linarith) (show 0 < b + c + d from by linarith), 
            mul_pos (show 0 < a + b + c from by linarith) (show 0 < a + c + d from by linarith), 
            mul_pos (show 0 < a + b + d from by linarith) (show 0 < b + c + d from by linarith), 
            mul_pos (show 0 < a + b + d from by linarith) (show 0 < a + c + d from by linarith), 
            mul_pos (show 0 < b + c + d from by linarith) (show 0 < a + c + d from by linarith)
          ]
        all_goals positivity
      linarith
    linarith

  have h2 : S < 2 := by
    rw [hS]
    have h1 : 0 < a := ha
    have h2 : 0 < b := hb
    have h3 : 0 < c := hc
    have h4 : 0 < d := hd
    have h5 : 0 < a + b + c := by linarith
    have h6 : 0 < a + b + d := by linarith
    have h7 : 0 < b + c + d := by linarith
    have h8 : 0 < a + c + d := by linarith
    have h10 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
      have pos1 : 0 < (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) := by positivity
      have h10 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 < 0 := by
        have h11 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 =
            ( a * (a + b + c) * (b + c + d) * (a + c + d) + b * (a + b + d) * (b + c + d) * (a + c + d) + c * (a + b + d) * (a + b + c) * (a + c + d) + d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) ) / ( (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) ) := by
          field_simp
          ring
        rw [h11]
        apply div_neg_of_neg_of_pos
        · -- Show the numerator is negative
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
              mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
              mul_pos hb hc, mul_pos hb hd, 
              mul_pos hc hd, 
              mul_pos (show 0 < a + b + c from by linarith) (show 0 < a + b + d from by linarith), 
              mul_pos (show 0 < a + b + c from by linarith) (show 0 < b + c + d from by linarith), 
              mul_pos (show 0 < a + b + c from by linarith) (show 0 < a + c + d from by linarith), 
              mul_pos (show 0 < a + b + d from by linarith) (show 0 < b + c + d from by linarith), 
              mul_pos (show 0 < a + b + d from by linarith) (show 0 < a + c + d from by linarith), 
              mul_pos (show 0 < b + c + d from by linarith) (show 0 < a + c + d from by linarith)
            ]
        all_goals positivity
      linarith
    linarith
  constructor
  · exact h1
  · exact h2