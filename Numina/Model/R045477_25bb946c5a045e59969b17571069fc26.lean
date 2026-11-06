import Mathlib
open Real

theorem inequalities_597760 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h3 : Real.log (a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c)) = 2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c := by
    have h3_1 : Real.log (a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c)) = Real.log (a ^ (2 * a)) + Real.log (b ^ (2 * b)) + Real.log (c ^ (2 * c)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    rw [h3_1]
    have h3_2 : Real.log (a ^ (2 * a)) = 2 * a * Real.log a := by
      rw [Real.log_rpow]
      all_goals nlinarith
    have h3_3 : Real.log (b ^ (2 * b)) = 2 * b * Real.log b := by
      rw [Real.log_rpow]
      all_goals nlinarith
    have h3_4 : Real.log (c ^ (2 * c)) = 2 * c * Real.log c := by
      rw [Real.log_rpow]
      all_goals nlinarith
    rw [h3_2, h3_3, h3_4]

  have h4 : Real.log (a ^ (b + c) * b ^ (c + a) * c ^ (a + b)) = (b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c := by
    have h4_1 : Real.log (a ^ (b + c) * b ^ (c + a) * c ^ (a + b)) = Real.log (a ^ (b + c)) + Real.log (b ^ (c + a)) + Real.log (c ^ (a + b)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    rw [h4_1]
    have h4_2 : Real.log (a ^ (b + c)) = (b + c) * Real.log a := by
      rw [Real.log_rpow]
      all_goals nlinarith
    have h4_3 : Real.log (b ^ (c + a)) = (c + a) * Real.log b := by
      rw [Real.log_rpow]
      all_goals nlinarith
    have h4_4 : Real.log (c ^ (a + b)) = (a + b) * Real.log c := by
      rw [Real.log_rpow]
      all_goals nlinarith
    rw [h4_2, h4_3, h4_4]

  have h5 : 2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c ≥ (b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c := by
    have h6 : (a - b) * (Real.log a - Real.log b) ≥ 0 := by
      by_cases h : a ≥ b
      · -- If a >= b, then ln(a) >= ln(b).
        have h7 : Real.log a ≥ Real.log b := by
          apply Real.log_le_log
          all_goals linarith
        nlinarith
      · -- If a < b, then ln(a) < ln(b).
        have h7 : Real.log a < Real.log b := by
          apply Real.log_lt_log
          all_goals linarith
        nlinarith
    have h7 : (a - c) * (Real.log a - Real.log c) ≥ 0 := by
      by_cases h : a ≥ c
      · -- If a >= c, then ln(a) >= ln(c).
        have h8 : Real.log a ≥ Real.log c := by
          apply Real.log_le_log
          all_goals linarith
        nlinarith
      · -- If a < c, then ln(a) < ln(c).
        have h8 : Real.log a < Real.log c := by
          apply Real.log_lt_log
          all_goals linarith
        nlinarith
    have h8 : (b - c) * (Real.log b - Real.log c) ≥ 0 := by
      by_cases h : b ≥ c
      · -- If b >= c, then ln(b) >= ln(c).
        have h9 : Real.log b ≥ Real.log c := by
          apply Real.log_le_log
          all_goals linarith
        nlinarith
      · -- If b < c, then ln(b) < ln(c).
        have h9 : Real.log b < Real.log c := by
          apply Real.log_lt_log
          all_goals linarith
        nlinarith
    have h9 : (a - b) * (Real.log a - Real.log b) + (a - c) * (Real.log a - Real.log c) + (b - c) * (Real.log b - Real.log c) ≥ 0 := by
      linarith [h6, h7, h8]
    have h10 : 2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c - ((b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c) ≥ 0 := by
      have h11 : 2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c - ((b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c) =
          (a - b) * (Real.log a - Real.log b) + (a - c) * (Real.log a - Real.log c) + (b - c) * (Real.log b - Real.log c) := by
        ring
      linarith [h11, h9]
    linarith

  have h11 : Real.log (a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c)) ≥ Real.log (a ^ (b + c) * b ^ (c + a) * c ^ (a + b)) := by
    linarith [h3, h4, h5]

  have h10 : a ^ (2 * a) * b ^ (2 * b) * c ^ (2 * c) ≥ a ^ (b + c) * b ^ (c + a) * c ^ (a + b) := by
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h11

  exact h10