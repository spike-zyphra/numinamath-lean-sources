import Mathlib

theorem inequalities_1248 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (1 / (6 * a + 5 * b + 3 * c) + 1 / (6 * b + 5 * c + 3 * a) +
     1 / (6 * c + 5 * a + 3 * b)) ≤
    (a ^ 2 + b ^ 2 + c ^ 2) / 14 := by

  have h1 : 0 < 6 * a + 5 * b + 3 * c := by positivity
  have h2 : 0 < 6 * b + 5 * c + 3 * a := by positivity
  have h3 : 0 < 6 * c + 5 * a + 3 * b := by positivity

  have h5 : (1 / (6 * a + 5 * b + 3 * c) + 1 / (6 * b + 5 * c + 3 * a) +
      1 / (6 * c + 5 * a + 3 * b)) - (a ^ 2 + b ^ 2 + c ^ 2) / 14 ≤ 0 := by
    have h6 : (1 / (6 * a + 5 * b + 3 * c) + 1 / (6 * b + 5 * c + 3 * a) +
        1 / (6 * c + 5 * a + 3 * b)) - (a ^ 2 + b ^ 2 + c ^ 2) / 14 =
        ( (14 * ((6 * b + 5 * c + 3 * a) * (6 * c + 5 * a + 3 * b) + (6 * a + 5 * b + 3 * c) * (6 * c + 5 * a + 3 * b) + (6 * a + 5 * b + 3 * c) * (6 * b + 5 * c + 3 * a)) ) - (a^2 + b^2 + c^2) * ( (6 * a + 5 * b + 3 * c) * (6 * b + 5 * c + 3 * a) * (6 * c + 5 * a + 3 * b) ) ) / ( (6 * a + 5 * b + 3 * c) * (6 * b + 5 * c + 3 * a) * (6 * c + 5 * a + 3 * b) * 14 ) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonpos_of_nonpos_of_nonneg
    -- Show the numerator is non-positive. 
    have h8 : (14 * ((6 * b + 5 * c + 3 * a) * (6 * c + 5 * a + 3 * b) + (6 * a + 5 * b + 3 * c) * (6 * c + 5 * a + 3 * b) + (6 * a + 5 * b + 3 * c) * (6 * b + 5 * c + 3 * a)) ) - (a^2 + b^2 + c^2) * ( (6 * a + 5 * b + 3 * c) * (6 * b + 5 * c + 3 * a) * (6 * c + 5 * a + 3 * b) ) ≤ 0 := by
      nlinarith [ sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
                sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
                  sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
                    habc
                    ]
    linarith
    -- Show the denominator is non-negative. 
    positivity

  linarith