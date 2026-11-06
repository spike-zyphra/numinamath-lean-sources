import Mathlib

open Real

theorem inequalities_262895 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) ≥ 1 := by
   have h1 : 0 < 2 * a + 1 := by
    linarith
   have h2 : 0 < 2 * b + 1 := by
    linarith
   have h3 : 0 < 2 * c + 1 := by
    linarith
   have h8 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1 ≥ 0 := by
     have pos1 : (2 * a + 1) * (2 * b + 1) * (2 * c + 1) > 0 := by
       positivity
     have h6 : (1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1) =
          ((2 * b + 1) * (2 * c + 1) + (2 * a + 1) * (2 * c + 1) + (2 * a + 1) * (2 * b + 1) - (2 * a + 1) * (2 * b + 1) * (2 * c + 1)) / ((2 * a + 1) * (2 * b + 1) * (2 * c + 1)) := by
       field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
       ring
     rw [h6] at *
     apply div_nonneg
     -- Show that the numerator is positive
     nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
     ]
     -- Show that the denominator is positive
     positivity
   linarith [h8]