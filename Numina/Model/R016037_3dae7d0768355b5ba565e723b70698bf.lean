import Mathlib

theorem inequalities_601886 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h2 : a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c) ≥ a ^ (b + c) * b ^ (c + a) * c ^ (a + b) := by
    have h3 : Real.log (a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c)) ≥ Real.log (a ^ (b + c) * b ^ (c + a) * c ^ (a + b) ) := by
      have h4 : Real.log (a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c)) =
          Real.log (a ^ (2 * a)) + Real.log (b ^ (2 * b)) + Real.log (c ^ (2 * c)) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have h5 : Real.log (a ^ (b + c) * b ^ (c + a) * c ^ (a + b)) =
          Real.log (a ^ (b + c)) + Real.log (b ^ (c + a)) + Real.log (c ^ (a + b)) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have h6 : Real.log (a ^ (2 * a)) = 2 * a * Real.log a := by
        rw [Real.log_rpow]
        all_goals nlinarith
      have h7 : Real.log (b ^ (2 * b)) = 2 * b * Real.log b := by
        rw [Real.log_rpow]
        all_goals nlinarith
      have h8 : Real.log (c ^ (2 * c)) = 2 * c * Real.log c := by
        rw [Real.log_rpow]
        all_goals nlinarith
      have h9 : Real.log (a ^ (b + c)) = (b + c) * Real.log a := by
        rw [Real.log_rpow]
        all_goals nlinarith
      have h10 : Real.log (b ^ (c + a)) = (c + a) * Real.log b := by
        rw [Real.log_rpow]
        all_goals nlinarith
      have h11 : Real.log (c ^ (a + b)) = (a + b) * Real.log c := by
        rw [Real.log_rpow]
        all_goals nlinarith
      rw [h4, h5, h6, h7, h8, h9, h10, h11]
      have h12 : (a - b) * (Real.log a - Real.log b) ≥ 0 := by
        by_cases h : a ≥ b
        · -- If a ≥ b, then log a ≥ log b.
          have h13 : Real.log a ≥ Real.log b := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If a < b, then log a < log b.
          have h14 : Real.log a < Real.log b := by
            apply Real.log_lt_log
            all_goals linarith
          nlinarith
      have h13 : (a - c) * (Real.log a - Real.log c) ≥ 0 := by
        by_cases h : a ≥ c
        · -- If a ≥ c, then log a ≥ log c.
          have h14 : Real.log a ≥ Real.log c := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If a < c, then log a < log c.
          have h15 : Real.log a < Real.log c := by
            apply Real.log_lt_log
            all_goals linarith
          nlinarith
      have h14 : (b - c) * (Real.log b - Real.log c) ≥ 0 := by
        by_cases h : b ≥ c
        · -- If b ≥ c, then log b ≥ log c.
          have h15 : Real.log b ≥ Real.log c := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If b < c, then log b < log c.
          have h16 : Real.log b < Real.log c := by
            apply Real.log_lt_log
            all_goals linarith
          nlinarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (Real.log a - Real.log b), sq_nonneg (Real.log a - Real.log c), sq_nonneg (Real.log b - Real.log c)]
    have h4 : a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c) ≥ a ^ (b + c) * b ^ (c + a) * c ^ (a + b) := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp at h3
      linarith
    exact h4
  exact h2