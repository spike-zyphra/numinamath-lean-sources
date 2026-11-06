import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_138640
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  2 < ((a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a*b*c)) ∧
  ((a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a*b*c)) ≤ 3 := by

  rcases h₀ with ⟨ha, hb, hc⟩

  constructor
  · -- Show that 2 < expression
    have h4 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h5 : ((a + b) / c + (b + c) / a + (c + a) / b - (a^3 + b^3 + c^3) / (a * b * c)) > 2 := by

      have h6 : ((a + b) / c + (b + c) / a + (c + a) / b - (a^3 + b^3 + c^3) / (a * b * c)) =
          ((a + b) * a * b + (b + c) * b * c + (c + a) * a * c - (a^3 + b^3 + c^3)) / (a * b * c) := by 
        field_simp
        ring

      rw [h6]

      apply (lt_div_iff₀ (by positivity)).mpr

      nlinarith [sq_pos_of_pos  (show (0 : ℝ) < a by linarith), 
          sq_pos_of_pos  (show (0 : ℝ) < b by linarith), 
          sq_pos_of_pos  (show (0 : ℝ) < c by linarith), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (show (0 : ℝ) < a + b - c by linarith) (show (0 : ℝ) < a + c - b by linarith), 
          mul_pos (show (0 : ℝ) < a + c - b by linarith) (show (0 : ℝ) < b + c - a by linarith), 
          mul_pos (show (0 : ℝ) < a + b - c by linarith) (show (0 : ℝ) < b + c - a by linarith)]

    linarith
  · -- Show that expression ≤ 3
    have h4 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h7 : ((a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a * b * c)) ≤ 3 := by

      have h8 : ((a + b)/c + (b + c)/a + (c + a)/b - (a^3 + b^3 + c^3)/(a * b * c)) =
          ((a + b) * a * b + (b + c) * b * c + (c + a) * a * c - (a^3 + b^3 + c^3)) / (a * b * c) := by
        field_simp
        ring

      rw [h8]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
          sq_pos_of_pos (show (0 : ℝ) < a by linarith), 
          sq_pos_of_pos (show (0 : ℝ) < b by linarith), 
          sq_pos_of_pos (show (0 : ℝ) < c by linarith), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show (0 : ℝ) < a + b - c by linarith) (show (0 : ℝ) < a + c - b by linarith), 
          mul_pos (show (0 : ℝ) < a + c - b by linarith) (show (0 : ℝ) < b + c - a by linarith), 
          mul_pos (show (0 : ℝ) < a + b - c by linarith) (show (0 : ℝ) < b + c - a by linarith), 
          mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < a * b by nlinarith), 
          mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < b * c by nlinarith), 
          mul_pos (show (0 : ℝ) < c by linarith) (show (0 : ℝ) < a * c by nlinarith)]
    linarith