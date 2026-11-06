import Mathlib

theorem inequalities_276641 (a b c : ℝ) (h : a * b * c ≠ 0) :
    a^4 / (4 * a^4 + b^4 + c^4) +
    b^4 / (a^4 + 4 * b^4 + c^4) +
    c^4 / (a^4 + b^4 + 4 * c^4) ≤ 1 / 2 := by

  have ha1 : a ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have hb1 : b ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have hc1 : c ≠ 0 := by 
    by_contra h1
    have h2 : a * b * c = 0 := by 
      rw [h1]
      norm_num
    contradiction

  have h1 : 0 < 4 * a^4 + b^4 + c^4 := by
    positivity

  have h2 : 0 < a^4 + 4 * b^4 + c^4 := by
    positivity

  have h3 : 0 < a^4 + b^4 + 4 * c^4 := by
    positivity
  
  have h4 : a^4 / (4 * a^4 + b^4 + c^4) +
    b^4 / (a^4 + 4 * b^4 + c^4) +
    c^4 / (a^4 + b^4 + 4 * c^4) - 1 / 2 ≤ 0 := by

    have h5 : a^4 / (4 * a^4 + b^4 + c^4) +
    b^4 / (a^4 + 4 * b^4 + c^4) +
    c^4 / (a^4 + b^4 + 4 * c^4) - 1 / 2 =
    (2 * (a^4 * (a^4 + 4 * b^4 + c^4) * (a^4 + b^4 + 4 * c^4) + 
    b^4 * (4 * a^4 + b^4 + c^4) * (a^4 + b^4 + 4 * c^4) + 
    c^4 * (4 * a^4 + b^4 + c^4) * (a^4 + 4 * b^4 + c^4)) - 
    (4 * a^4 + b^4 + c^4) * (a^4 + 4 * b^4 + c^4) * (a^4 + b^4 + 4 * c^4)) / (2 * (4 * a^4 + b^4 + c^4) * (a^4 + 4 * b^4 + c^4) * (a^4 + b^4 + 4 * c^4)) := by
      field_simp
      ring

    rw [h5] at *
    
    apply div_nonpos_of_nonpos_of_nonneg

    · -- Show the numerator is non-positive
      nlinarith [sq_nonneg (a^4 - b^4), sq_nonneg (a^4 - c^4), sq_nonneg (b^4 - c^4), 
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2), 
          sq_nonneg (a^2 + b^2 - c^2), sq_nonneg (a^2 - b^2 + c^2), sq_nonneg (-a^2 + b^2 + c^2), 
          sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c),
          sq_nonneg (a^4 + b^4 - c^4), sq_nonneg (a^4 - b^4 + c^4), sq_nonneg (-a^4 + b^4 + c^4), 
          mul_pos (show 0 < a^2 by positivity) (show 0 < b^2 by positivity), 
          mul_pos (show 0 < a^2 by positivity) (show 0 < c^2 by positivity), 
          mul_pos (show 0 < b^2 by positivity) (show 0 < c^2 by positivity), 
          mul_pos (show 0 < a^4 by positivity) (show 0 < b^4 by positivity), 
          mul_pos (show 0 < a^4 by positivity) (show 0 < c^4 by positivity), 
          mul_pos (show 0 < b^4 by positivity) (show 0 < c^4 by positivity)
        ]
    
    · -- Show the denominator is non-negative
      positivity
  
  linarith