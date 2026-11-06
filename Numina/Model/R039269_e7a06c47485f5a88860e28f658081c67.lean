import Mathlib

theorem inequalities_46346 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * a ^ 2 * b ^ 2 / (a ^ 5 + b ^ 5) + 2 * b ^ 2 * c ^ 2 / (b ^ 5 + c ^ 5) +
    2 * c ^ 2 * a ^ 2 / (c ^ 5 + a ^ 5) ≤
    (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) := by

  have h1 : 2 * a ^ 2 * b ^ 2 / (a ^ 5 + b ^ 5) ≤ (a + b) / (2 * a * b) := by
    have h2 : 0 < a ^ 5 + b ^ 5 := by positivity
    have h3 : 0 < 2 * a * b := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a ^ 3 - b ^ 3), 
          sq_nonneg (a ^ 2 * b - a * b ^ 2), sq_nonneg (a * b * (a - b)), 
          sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), 
          mul_pos ha hb, mul_pos (show 0 < a ^ 2 by positivity) (show 0 < b ^ 2 by positivity), 
          sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 3 - b ^ 3), 
          sq_nonneg (a * b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
          sq_nonneg (a ^ 2 * b ^ 2), sq_nonneg (a * b ^ 2), sq_nonneg (a ^ 2 * b), sq_nonneg (a * b * (a * b)), 
          sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 3 - b ^ 3)
        ]
  
  have h2 : 2 * b ^ 2 * c ^ 2 / (b ^ 5 + c ^ 5) ≤ (b + c) / (2 * b * c) := by 
    have h4 : 0 < b ^ 5 + c ^ 5 := by positivity 
    have h5 : 0 < 2 * b * c := by positivity 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b ^ 3 - c ^ 3), 
          sq_nonneg (b ^ 2 * c - b * c ^ 2), sq_nonneg (b * c * (b - c)), 
          sq_nonneg (b ^ 3 - c ^ 3), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), 
          mul_pos hb hc, mul_pos (show 0 < b ^ 2 by positivity) (show 0 < c ^ 2 by positivity), 
          sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 3 - c ^ 3), 
          sq_nonneg (b * c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), 
          sq_nonneg (b ^ 2 * c ^ 2), sq_nonneg (b * c ^ 2), sq_nonneg (b ^ 2 * c), sq_nonneg (b * c * (b * c)), 
          sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 3 - c ^ 3)
        ]

  have h3 : 2 * c ^ 2 * a ^ 2 / (c ^ 5 + a ^ 5) ≤ (c + a) / (2 * c * a) := by 
    have h6 : 0 < c ^ 5 + a ^ 5 := by positivity 
    have h7 : 0 < 2 * c * a := by positivity 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c ^ 3 - a ^ 3), 
          sq_nonneg (c ^ 2 * a - c * a ^ 2), sq_nonneg (c * a * (c - a)), 
          sq_nonneg (c ^ 3 - a ^ 3), sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), 
          mul_pos hc ha, mul_pos (show 0 < c ^ 2 by positivity) (show 0 < a ^ 2 by positivity), 
          sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c ^ 3 - a ^ 3), 
          sq_nonneg (c * a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), 
          sq_nonneg (c ^ 2 * a ^ 2), sq_nonneg (c * a ^ 2), sq_nonneg (c ^ 2 * a), sq_nonneg (c * a * (c * a)), 
          sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c ^ 3 - a ^ 3)
        ]

  linarith [h1, h2, h3]