import Mathlib

open Real Set

theorem algebra_125389 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : ℝ) (hx : x = a / (a + b + d) + b / (b + c + a) + c / (c + d + b) + d / (d + a + c)) :
    x ∈ Ioo 1 2 := by
  rw [hx]
  constructor
  · -- Prove that the expression is greater than 1
    have h1 : a / (a + b + d) + b / (b + c + a) + c / (c + d + b) + d / (d + a + c) > 1 := by
      have h2 : 0 < (a + b + d) := by positivity
      have h3 : 0 < (b + c + a) := by positivity
      have h4 : 0 < (c + d + b) := by positivity
      have h5 : 0 < (d + a + c) := by positivity
      have h6 : a / (a + b + d) + b / (b + c + a) + c / (c + d + b) + d / (d + a + c) - 1 > 0 := by
        have h7 : a / (a + b + d) + b / (b + c + a) + c / (c + d + b) + d / (d + a + c) - 1 =
            ( a * (b + c + a) * (c + d + b) * (d + a + c) +
              b * (a + b + d) * (c + d + b) * (d + a + c) +
              c * (a + b + d) * (b + c + a) * (d + a + c) +
              d * (a + b + d) * (b + c + a) * (c + d + b) - (a + b + d) * (b + c + a) * (c + d + b) * (d + a + c) )
              / ( (a + b + d) * (b + c + a) * (c + d + b) * (d + a + c) ) := by
          field_simp
          ring
        rw [h7] at *
        apply div_pos
        · -- Show the numerator is positive
          ring_nf
          nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd,
              mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
          ]
        all_goals
          positivity
      linarith
    linarith
  · -- Prove that the expression is less than 2
    have h2 : a / (a + b + d) + b / (b + c + a) + c / (c + d + b) + d / (d + a + c) < 2 := by
      have h2 : 0 < (a + b + d) := by positivity
      have h3 : 0 < (b + c + a) := by positivity
      have h4 : 0 < (c + d + b) := by positivity
      have h5 : 0 < (d + a + c) := by positivity
      have h6 : a / (a + b + d) + b / (b + c + a) + c / (c + d + b) + d / (d + a + c) - 2 < 0 := by
        have h7 : a / (a + b + d) + b / (b + c + a) + c / (c + d + b) + d / (d + a + c) - 2 =
            ( a * (b + c + a) * (c + d + b) * (d + a + c) +
              b * (a + b + d) * (c + d + b) * (d + a + c) +
              c * (a + b + d) * (b + c + a) * (d + a + c) +
              d * (a + b + d) * (b + c + a) * (c + d + b) - 2 * ( (a + b + d) * (b + c + a) * (c + d + b) * (d + a + c) ) )
              / ( (a + b + d) * (b + c + a) * (c + d + b) * (d + a + c) ) := by
          field_simp
          ring
        rw [h7] at *
        apply div_neg_of_neg_of_pos
        · -- Show the numerator is negative
          ring_nf
          nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd,
              mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
          ]
        all_goals
          positivity
      linarith
    linarith