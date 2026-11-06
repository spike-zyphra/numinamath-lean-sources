import Mathlib

theorem inequalities_312077 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b / (3 * a + 4 * b + 5 * c) + b * c / (3 * b + 4 * c + 5 * a) +
    c * a / (3 * c + 4 * a + 5 * b) ≤
    1 / 12 * (a + b + c) := by
  have h1 : 0 < 3 * a + 4 * b + 5 * c := by
    positivity
  have h2 : 0 < 3 * b + 4 * c + 5 * a := by
    positivity
  have h3 : 0 < 3 * c + 4 * a + 5 * b := by
    positivity
  
  have h4 : a * b / (3 * a + 4 * b + 5 * c) + b * c / (3 * b + 4 * c + 5 * a) + c * a / (3 * c + 4 * a + 5 * b) - 1 / 12 * (a + b + c) ≤ 0 := by
    have h5 : 0 < (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) := by 
      positivity

    have eq : a * b / (3 * a + 4 * b + 5 * c) + b * c / (3 * b + 4 * c + 5 * a) + c * a / (3 * c + 4 * a + 5 * b) - 1 / 12 * (a + b + c) =
        (a * b * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) + b * c * (3 * a + 4 * b + 5 * c) * (3 * c + 4 * a + 5 * b) + c * a * (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) - 1 / 12 * (a + b + c) * ((3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b))) / ((3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b)) := by
      field_simp
      ring

    rw [eq]

    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show numerator is ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                    sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
                    sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
                    sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
                    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
                ]
    · -- Show denominator is ≥ 0
      positivity
  
  linarith [h4]