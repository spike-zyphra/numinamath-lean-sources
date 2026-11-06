import Mathlib

theorem negated_inequalities_69089 (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (3 / 5 : ℚ) ≤ (b + c - a)^2 / ((b + c)^2 + a^2) + (c + a - b)^2 / ((c + a)^2 + b^2) + (a + b - c)^2 / ((a + b)^2 + c^2) := by

  have h1 : 0 < (a : ℚ) := by exact_mod_cast ha
  have h2 : 0 < (b : ℚ) := by exact_mod_cast hb
  have h3 : 0 < (c : ℚ) := by exact_mod_cast hc

  have h4 : (b + c - a : ℚ) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b : ℚ) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c : ℚ) ^ 2 / ((a + b) ^ 2 + c ^ 2) ≥ (3 / 5 : ℚ) := by

    have h5 : 0 < ((b + c) ^ 2 + a ^ 2 : ℚ) := by
      positivity
    have h6 : 0 < ((c + a) ^ 2 + b ^ 2 : ℚ) := by
      positivity
    have h7 : 0 < ((a + b) ^ 2 + c ^ 2 : ℚ) := by
      positivity

    have h8 : (b + c - a : ℚ) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b : ℚ) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c : ℚ) ^ 2 / ((a + b) ^ 2 + c ^ 2) - (3 / 5 : ℚ) ≥ 0 := by
      have h9 : (b + c - a : ℚ) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b : ℚ) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c : ℚ) ^ 2 / ((a + b) ^ 2 + c ^ 2) - (3 / 5 : ℚ) =
          (5 * ((b + c - a) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((c + a - b : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((a + b - c : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2)) - 3 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) / (5 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) := by
        field_simp
        ring
      rw [h9]
      apply div_nonneg
      have h13 : 0 ≤ 5 * ((b + c - a : ℚ) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((c + a - b : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((a + b - c : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2)) - 3 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) := by
        have h13 : (0 : ℚ) ≤ 5 * ((b + c - a : ℚ) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((c + a - b : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((a + b - c : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2)) - 3 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) := by
          have h13' : 0 ≤ 5 * ((b + c - a : ℤ) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((c + a - b : ℤ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((a + b - c : ℤ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2)) - 3 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) := by
            nlinarith [sq_nonneg (a * b - b * c : ℤ), sq_nonneg (b * c - c * a : ℤ), sq_nonneg (c * a - a * b : ℤ),
              sq_nonneg (a - b : ℤ), sq_nonneg (b - c : ℤ), sq_nonneg (c - a : ℤ),
              sq_nonneg (a * (a - b) : ℤ), sq_nonneg (a * (a - c) : ℤ),
              sq_nonneg (b * (b - c) : ℤ), sq_nonneg (b * (b - a) : ℤ),
              sq_nonneg (c * (c - a) : ℤ), sq_nonneg (c * (c - b) : ℤ),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]
          have h13'' : (0 : ℚ) ≤ 5 * ((b + c - a : ℚ) ^ 2 * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((c + a - b : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((a + b) ^ 2 + c ^ 2)) + 5 * ((a + b - c : ℚ) ^ 2 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2)) - 3 * ((b + c) ^ 2 + a ^ 2) * ((c + a) ^ 2 + b ^ 2) * ((a + b) ^ 2 + c ^ 2) := by
            exact_mod_cast h13'
          linarith
        linarith
      all_goals
        positivity
    linarith
  linarith