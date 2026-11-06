import Mathlib

theorem inequalities_3072 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a + 2 * b + 3 * c) + 1 / (b + 2 * c + 3 * a) + 1 / (c + 2 * a + 3 * b) ≤
    1 / (6 * a) + 1 / (6 * b) + 1 / (6 * c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 1 / (a + 2 * b + 3 * c) + 1 / (b + 2 * c + 3 * a) + 1 / (c + 2 * a + 3 * b) - (1 / (6 * a) + 1 / (6 * b) + 1 / (6 * c)) ≤ 0 := by
    have h2 : 0 < (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) := by
      positivity
    have h3 : (1 / (a + 2 * b + 3 * c) + 1 / (b + 2 * c + 3 * a) + 1 / (c + 2 * a + 3 * b) - (1 / (6 * a) + 1 / (6 * b) + 1 / (6 * c)) ) =
        ( (6 * a) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * b) * (6 * c) + 
          (6 * a) * (a + 2 * b + 3 * c) * (c + 2 * a + 3 * b) * (6 * b) * (6 * c) + 
          (6 * a) * (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (6 * b) * (6 * c) - 
          ( (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * b) * (6 * c) + 
            (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * c) + 
            (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) ) ) / 
        ( (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) ) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonpos_of_nonpos_of_nonneg
    -- Numerator ≤ 0
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    -- Denominator ≥ 0
    positivity
  linarith