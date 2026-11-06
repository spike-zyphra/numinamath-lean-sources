import Mathlib

open Real

theorem inequalities_1140 (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k) :
  a/(b+k) + b/(c+k) + c/(a+k) ≥ 3*(a+b+c)/(a+b+c+3*k) := by 
  have h11 : a/(b+k) + b/(c+k) + c/(a+k) - 3*(a+b+c)/(a+b+c+3*k) ≥ 0 := by
    have pos1 : 0 < (b + k) := by linarith
    have pos2 : 0 < (c + k) := by linarith
    have pos3 : 0 < (a + k) := by linarith
    have pos4 : 0 < (a + b + c + 3 * k) := by linarith
    have h12 : a/(b+k) + b/(c+k) + c/(a+k) - 3*(a+b+c)/(a+b+c+3*k) =
          ( a * (c + k) * (a + k) * (a + b + c + 3 * k) + b * (b + k) * (a + k) * (a + b + c + 3 * k) + c * (b + k) * (c + k) * (a + b + c + 3 * k) - 3*(a + b + c)*(b + k) * (c + k) * (a + k) ) / ((b + k) * (c + k) * (a + k) * (a + b + c + 3 * k)) := by
      field_simp
      ring
    rw [h12] at *
    apply div_nonneg
    -- Need to prove the numerator is non-negative.
    have h8 : a * (c + k) * (a + k) * (a + b + c + 3 * k) + b * (b + k) * (a + k) * (a + b + c + 3 * k) + 
      c * (b + k) * (c + k) * (a + b + c + 3 * k) - 3 * (a + b + c) * (b + k) * (c + k) * (a + k) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a * k - b * k), sq_nonneg (b * k - c * k), sq_nonneg (c * k - a * k),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
          sq_nonneg ((a + k) - (b + k)), sq_nonneg ((b + k) - (c + k)), sq_nonneg ((c + k) - (a + k)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hk, 
          mul_pos hb hc, mul_pos hb hk, mul_pos hc hk, 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < a * k by nlinarith), 
          mul_pos (show 0 < b * k by nlinarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < a * k by nlinarith) (show 0 < b * c by nlinarith)
          ]
    linarith
    all_goals
      positivity
  linarith [h11]