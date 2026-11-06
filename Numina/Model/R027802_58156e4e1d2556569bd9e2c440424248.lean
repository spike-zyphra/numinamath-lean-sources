import Mathlib

open Real
open scoped BigOperators

theorem inequalities_319285 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : (b^2 + c^2 - a^2)/(2*b*c) + (a^2 + c^2 - b^2)/(2*a*c) +
    (a^2 + b^2 - c^2)/(2*a*b) > 1) :
  a + b > c ∧ a + c > b ∧ b + c > a := by
  have h1 : a * (b ^ 2 + c ^ 2 - a ^ 2) + b * (a ^ 2 + c ^ 2 - b ^ 2) + c * (a ^ 2 + b ^ 2 - c ^ 2) > 2 * a * b * c := by 
    have h1a : (b^2 + c^2 - a^2)/(2*b*c) + (a^2 + c^2 - b^2)/(2*a*c) + (a^2 + b^2 - c^2)/(2*a*b) - 1 > 0 := by
      linarith [h]
    
    have h2a : (b^2 + c^2 - a^2)/(2*b*c) + (a^2 + c^2 - b^2)/(2*a*c) + (a^2 + b^2 - c^2)/(2*a*b) - 1 =
        (a * (b^2 + c^2 - a^2) + b * (a^2 + c^2 - b^2) + c * (a^2 + b^2 - c^2) - 2 * a * b * c ) / (2 * a * b * c) := by
      field_simp
      ring

    rw [h2a] at h1a 
    apply (div_pos_iff_of_pos_right (by positivity)).mp at h1a 
    linarith

  have h2 : a + b > c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith),
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith),
      sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c)
    ]
  
  have h3 : a + c > b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith),
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith),
      sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c)
    ]
  
  have h4 : b + c > a := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith),
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith),
      sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c)
    ]
  
  exact ⟨h2, h3, h4⟩