import Mathlib

theorem inequalities_604047
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    a / (a^2 + 2 * a + 3) + b / (b^2 + 2 * b + 3) +
    c / (c^2 + 2 * c + 3) ≤ 1 / 2 := by
  have h1 : 0 < a * b := by apply mul_pos; exact ha; exact hb
  have h2 : 0 < b * c := by apply mul_pos; exact hb; exact hc
  have h3 : 0 < c * a := by apply mul_pos; exact hc; exact ha
  have h4 : a / (a^2 + 2 * a + 3) + b / (b^2 + 2 * b + 3) + c / (c^2 + 2 * c + 3) - 1 / 2 ≤ 0 := by
    have h5 : a / (a^2 + 2 * a + 3) + b / (b^2 + 2 * b + 3) + c / (c^2 + 2 * c + 3) - 1 / 2 ≤ 0 := by
      have h6 : a / (a^2 + 2 * a + 3) + b / (b^2 + 2 * b + 3) + c / (c^2 + 2 * c + 3) - 1 / 2 =
      (2 * a * (b^2 + 2 * b + 3) * (c^2 + 2 * c + 3) + 2 * b * (a^2 + 2 * a + 3) * (c^2 + 2 * c + 3) + 2 * c * (a^2 + 2 * a + 3) * (b^2 + 2 * b + 3) - (a^2 + 2 * a + 3) * (b^2 + 2 * b + 3) * (c^2 + 2 * c + 3)) / (2 * (a^2 + 2 * a + 3) * (b^2 + 2 * b + 3) * (c^2 + 2 * c + 3)) := by
        field_simp
        ring
      rw [h6]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show the numerator is ≤ 0
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1)]
      · -- Show the denominator is ≥ 0
        positivity
    linarith
  linarith
  all_goals
    nlinarith
    all_goals
      try nlinarith
      all_goals
        try ring_nf
        all_goals
          try nlinarith
          all_goals
            try linarith
            all_goals
              try nlinarith
              all_goals
                try nlinarith
                all_goals
                  try nlinarith
                  all_goals
                    try nlinarith
                    all_goals
                      try positivity
                      all_goals
                        try nlinarith
                        all_goals
                          try nlinarith
                          all_goals
                            try nlinarith