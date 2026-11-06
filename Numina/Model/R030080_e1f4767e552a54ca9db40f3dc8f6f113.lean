import Mathlib

theorem inequalities_63989 (a b c : ℝ) (h : a * b + b * c + c * a = 1) :
    3 ≤ ((a + b) ^ 2 + 1) / (c ^ 2 + 2) + ((b + c) ^ 2 + 1) / (a ^ 2 + 2) +
        ((c + a) ^ 2 + 1) / (b ^ 2 + 2) := by

  have h1 : 0 < c ^ 2 + 2 := by
    nlinarith [sq_nonneg c]

  have h2 : 0 < a ^ 2 + 2 := by
    nlinarith [sq_nonneg a]

  have h3 : 0 < b ^ 2 + 2 := by
    nlinarith [sq_nonneg b]

  have h4 : ((a + b) ^ 2 + 1) / (c ^ 2 + 2) + ((b + c) ^ 2 + 1) / (a ^ 2 + 2) + ((c + a) ^ 2 + 1) / (b ^ 2 + 2) - 3 ≥ 0 := by
    have h5 : ((a + b) ^ 2 + 1) / (c ^ 2 + 2) + ((b + c) ^ 2 + 1) / (a ^ 2 + 2) + ((c + a) ^ 2 + 1) / (b ^ 2 + 2) - 3 =
        ( ((a + b) ^ 2 + 1) * (a ^ 2 + 2) * (b ^ 2 + 2) + ((b + c) ^ 2 + 1) * (c ^ 2 + 2) * (b ^ 2 + 2) + ((c + a) ^ 2 + 1) * (c ^ 2 + 2) * (a ^ 2 + 2) - 3 * (c ^ 2 + 2) * (a ^ 2 + 2) * (b ^ 2 + 2) ) / ( (c ^ 2 + 2) * (a ^ 2 + 2) * (b ^ 2 + 2) ) := by
      field_simp [h1, h2, h3]
      ring
    rw [h5]

    have h6 : ( ((a + b) ^ 2 + 1) * (a ^ 2 + 2) * (b ^ 2 + 2) + ((b + c) ^ 2 + 1) * (c ^ 2 + 2) * (b ^ 2 + 2) + ((c + a) ^ 2 + 1) * (c ^ 2 + 2) * (a ^ 2 + 2) - 3 * (c ^ 2 + 2) * (a ^ 2 + 2) * (b ^ 2 + 2) ) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          h, sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]

    have h7 : ( ((a + b) ^ 2 + 1) * (a ^ 2 + 2) * (b ^ 2 + 2) + ((b + c) ^ 2 + 1) * (c ^ 2 + 2) * (b ^ 2 + 2) + ((c + a) ^ 2 + 1) * (c ^ 2 + 2) * (a ^ 2 + 2) - 3 * (c ^ 2 + 2) * (a ^ 2 + 2) * (b ^ 2 + 2) ) / ( (c ^ 2 + 2) * (a ^ 2 + 2) * (b ^ 2 + 2) ) ≥ 0 := by
      apply div_nonneg
      linarith [h6]
      positivity

    linarith [h7]

  linarith [h4]