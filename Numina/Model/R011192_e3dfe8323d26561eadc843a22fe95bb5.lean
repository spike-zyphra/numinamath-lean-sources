import Mathlib
open Real Set
theorem Other_25033 (S  a b c d : ℝ) (hS : S = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d))
(ha : 0 < a) 
(hb : 0 < b) 
(hc : 0 < c) 
(hd : 0 < d) :
S ∈ Ioo 1 2 := by 
  rw [hS]
  constructor 
  · -- Prove that $1 < \frac{a}{a+b+d} + \frac{b}{a+b+c} + \frac{c}{b+c+d} + \frac{d}{a+c+d}$ 
    have h1 : 0 < a + b + d := by linarith 
    have h2 : 0 < a + b + c := by linarith
    have h3 : 0 < b + c + d := by linarith
    have h4 : 0 < a + c + d := by linarith
    have h5 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
      have h6 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 > 0 := by
        have h7 : (a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1) =
            ( a * (a + b + c) * (b + c + d) * (a + c + d) + 
              b * (a + b + d) * (b + c + d) * (a + c + d) + 
              c * (a + b + d) * (a + b + c) * (a + c + d) + 
              d * (a + b + d) * (a + b + c) * (b + c + d) - 
              (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)
            ) / ( (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) ) := by 
          field_simp
          ring
        rw [h7]
        apply div_pos
        · -- Show that the numerator is positive 
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
            mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
            sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd, 
            mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith), 
            mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith)
          ]
        · -- Show that the denominator is positive
          positivity 
      linarith
    linarith
  · -- Prove that $\frac{a}{a+b+d} + \frac{b}{a+b+c} + \frac{c}{b+c+d} + \frac{d}{a+c+d} < 2$ 
    have h1 : 0 < a + b + d := by linarith 
    have h2 : 0 < a + b + c := by linarith
    have h3 : 0 < b + c + d := by linarith
    have h4 : 0 < a + c + d := by linarith
    have h10 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by 
      have h11 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 < 0 := by 
        have h12 : a * (a + b + c) * (b + c + d) * (a + c + d) + 
            b * (a + b + d) * (b + c + d) * (a + c + d) + 
            c * (a + b + d) * (a + b + c) * (a + c + d) + 
            d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) < 0 := by 
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
              mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
              sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd, 
              mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith), 
              mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith)
            ]
        have h13 : (a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2) = 
            ( a * (a + b + c) * (b + c + d) * (a + c + d) + 
              b * (a + b + d) * (b + c + d) * (a + c + d) + 
              c * (a + b + d) * (a + b + c) * (a + c + d) + 
              d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)
            ) / ( (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) ) := by 
          field_simp
          ring
        rw [h13]
        apply div_neg_of_neg_of_pos
        · -- Show the numerator is negative
          linarith [h12]
        · -- Show the denominator is positive 
          positivity 
      linarith
    linarith