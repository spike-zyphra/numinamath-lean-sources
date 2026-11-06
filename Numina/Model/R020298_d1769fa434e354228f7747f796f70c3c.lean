import Mathlib.Tactic

theorem algebra_136801
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (x : ℝ)
    (hx : x = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) :
    1 < x ∧ x < 2 := by 
  rw [hx]
  constructor
  · -- Show that 1 < x
    have h2 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
      have h1 : 0 < (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) := by
        positivity
      have h3 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 > 0 := by
        have h4 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 =
            (a * (a + b + c) * (b + c + d) * (a + c + d) + 
             b * (a + b + d) * (b + c + d) * (a + c + d) + 
             c * (a + b + d) * (a + b + c) * (a + c + d) + 
             d * (a + b + d) * (a + b + c) * (b + c + d) - 
             (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) := by 
          field_simp
          ring
        rw [h4]
        have h5 : a * (a + b + c) * (b + c + d) * (a + c + d) + 
            b * (a + b + d) * (b + c + d) * (a + c + d) + 
            c * (a + b + d) * (a + b + c) * (a + c + d) + 
            d * (a + b + d) * (a + b + c) * (b + c + d) - 
            (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) > 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
                mul_pos hb hc, mul_pos hb hd, 
                mul_pos hc hd, 
                mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith), 
                mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith), 
                mul_pos (show 0 < a * d by nlinarith) (show 0 < b * c by nlinarith)
              ]
        have h6 : (a * (a + b + c) * (b + c + d) * (a + c + d) + 
            b * (a + b + d) * (b + c + d) * (a + c + d) + 
            c * (a + b + d) * (a + b + c) * (a + c + d) + 
            d * (a + b + d) * (a + b + c) * (b + c + d) - 
            (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) > 0 := by
          apply div_pos
          linarith
          all_goals linarith
        linarith
      linarith
    linarith
  · -- Show that x < 2
    have h3 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
      have h4 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 < 0 := by
        have h1 : 0 < (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) := by
          positivity
        have h5 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 =
            (a * (a + b + c) * (b + c + d) * (a + c + d) + 
             b * (a + b + d) * (b + c + d) * (a + c + d) + 
             c * (a + b + d) * (a + b + c) * (a + c + d) + 
             d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) := by 
          field_simp
          ring
        rw [h5]
        have h6 : a * (a + b + c) * (b + c + d) * (a + c + d) + 
            b * (a + b + d) * (b + c + d) * (a + c + d) + 
            c * (a + b + d) * (a + b + c) * (a + c + d) + 
            d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) < 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
                mul_pos hb hc, mul_pos hb hd, 
                mul_pos hc hd, 
                mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith), 
                mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith), 
                mul_pos (show 0 < a * d by nlinarith) (show 0 < b * c by nlinarith)
              ]
        have h2 : (a * (a + b + c) * (b + c + d) * (a + c + d) + 
            b * (a + b + d) * (b + c + d) * (a + c + d) + 
            c * (a + b + d) * (a + b + c) * (a + c + d) + 
            d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) < 0 := by
          apply div_neg_of_neg_of_pos
          nlinarith
          all_goals positivity
        linarith
      linarith
    linarith