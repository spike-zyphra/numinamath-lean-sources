import Mathlib

theorem inequalities_606017 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  |(a / b + b / c + c / a) - (a / c + c / b + b / a)| < 1 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : -1 < (a / b + b / c + c / a) - (a / c + c / b + b / a) := by 
    have h3 : (a / b + b / c + c / a) - (a / c + c / b + b / a) = (a^2 * c + a * b^2 + b * c^2 - (a^2 * b + a * c^2 + b^2 * c)) / (a * b * c) := by 
      field_simp 
      ring 
    rw [h3] at *
    have h4 : (a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a ^ 2 * b + a * c ^ 2 + b ^ 2 * c)) + (a * b * c) > 0 := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < a + c - b by linarith), 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith), 
          mul_pos (show 0 < a + c - b by linarith) (show 0 < b + c - a by linarith), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)
        ]
    have h5 : (a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a ^ 2 * b + a * c ^ 2 + b ^ 2 * c)) / (a * b * c) > -1 := by 
      have h6 : 0 < a * b * c := h1 
      apply (lt_div_iff₀ h6).mpr 
      nlinarith 
    linarith 
  have h3 : (a / b + b / c + c / a) - (a / c + c / b + b / a) < 1 := by 
    have h4 : (a / b + b / c + c / a) - (a / c + c / b + b / a) = (a^2 * c + a * b^2 + b * c^2 - (a^2 * b + a * c^2 + b^2 * c)) / (a * b * c) := by 
      field_simp 
      ring 
    rw [h4] at *
    have h5 : (a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a ^ 2 * b + a * c^2 + b^2 * c)) - (a * b * c) < 0 := by 
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < a + c - b by linarith), 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith), 
          mul_pos (show 0 < a + c - b by linarith) (show 0 < b + c - a by linarith), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)
        ]
    have h6 : (a ^ 2 * c + a * b ^ 2 + b * c^2 - (a^2 * b + a * c^2 + b^2 * c)) / (a * b * c) < 1 := by 
      have h7 : 0 < a * b * c := h1 
      apply (div_lt_iff₀ h7).mpr 
      nlinarith 
    linarith 
  apply abs_lt.mpr 
  constructor <;> linarith [h2, h3]