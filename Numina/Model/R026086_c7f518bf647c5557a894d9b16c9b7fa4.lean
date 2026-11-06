import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_133587
  (a b c : ℝ)
  (h : a > 0 ∧ b > 0 ∧ c > 0)
  (h1 : c < a + b)
  (h2 : b < a + c)
  (h3 : a < b + c) :
  3 < (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * a * c) / (c^2 + a^2) +
      (c^2 + 2 * a * b) / (a^2 + b^2) := by 
  rcases h with ⟨ha, hb, hc⟩
  have h4 : 0 < b^2 + c^2 := by 
    nlinarith [hb, hc, h1, h2, h3]
  have h5 : 0 < c^2 + a^2 := by
    nlinarith [ha, hc, h1, h2, h3]
  have h6 : 0 < a^2 + b^2 := by 
    nlinarith [ha, hb, h1, h2, h3]

  have h7 : (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * a * c) / (c^2 + a^2) +
      (c^2 + 2 * a * b) / (a^2 + b^2) - 3 > 0 := by
    have pos1 : 0 < (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2) := by
      positivity
    have h8 : (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * a * c) / (c^2 + a^2) +
        (c^2 + 2 * a * b) / (a^2 + b^2) - 3 =
      ((a^2 + 2 * b * c) * (c^2 + a^2) * (a^2 + b^2) + (b^2 + 2 * a * c) * (b^2 + c^2) * (a^2 + b^2) + (c^2 + 2 * a * b) * (b^2 + c^2) * (c^2 + a^2) - 3 * (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2)) / ((b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2)) := by 
      field_simp
      ring
    rw [h8] 
    apply div_pos
    · -- Prove the numerator is positive
      have h9 : (a^2 + 2 * b * c) * (c^2 + a^2) * (a^2 + b^2) + (b^2 + 2 * a * c) * (b^2 + c^2) * (a^2 + b^2) + (c^2 + 2 * a * b) * (b^2 + c^2) * (c^2 + a^2) > 3 * (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2) := by 
        have h8 : 0 < a * b * c := by
          apply mul_pos
          apply mul_pos
          all_goals linarith
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a^2 * b - b * c^2), sq_nonneg (b^2 * c - c * a^2), sq_nonneg (c^2 * a - a * b^2),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
            mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
            mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith), 
            mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
            mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), 
            mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), 
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
            sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos (show 0 < a by linarith) (show 0 < b * c by nlinarith)
          ]
      linarith [h9]
    · -- Prove the denominator is positive
      positivity
  linarith [h7]