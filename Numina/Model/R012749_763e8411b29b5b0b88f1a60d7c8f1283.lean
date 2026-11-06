import Mathlib

theorem inequalities_315892 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^(2 * a) * b^(2 * b) * c^(2 * c) ≥ a^(b + c) * b^(c + a) * c^(a + b) := by
  have h1 : a^(2 * a) * b^(2 * b) * c^(2 * c) = Real.exp (2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c) := by
    have h2 : a^(2 * a) = Real.exp (2 * a * Real.log a) := by
      rw [Real.rpow_def_of_pos ha]
      field_simp
      <;> linarith
    have h3 : b^(2 * b) = Real.exp (2 * b * Real.log b) := by
      rw [Real.rpow_def_of_pos hb]
      field_simp
      <;> linarith
    have h4 : c^(2 * c) = Real.exp (2 * c * Real.log c) := by
      rw [Real.rpow_def_of_pos hc]
      field_simp
      <;> linarith
    calc
      a^(2 * a) * b^(2 * b) * c^(2 * c) = Real.exp (2 * a * Real.log a) * Real.exp (2 * b * Real.log b) * Real.exp (2 * c * Real.log c) := by rw [h2, h3, h4]
      _ = Real.exp ((2 * a * Real.log a) + (2 * b * Real.log b) + (2 * c * Real.log c)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = Real.exp (2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c) := by ring
  have h5 : a^(b + c) * b^(c + a) * c^(a + b) = Real.exp ((b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c) := by
    have h6 : a^(b + c) = Real.exp ((b + c) * Real.log a) := by
      rw [Real.rpow_def_of_pos ha]
      field_simp
      <;> linarith
    have h7 : b^(c + a) = Real.exp ((c + a) * Real.log b) := by
      rw [Real.rpow_def_of_pos hb]
      field_simp
      <;> linarith
    have h8 : c^(a + b) = Real.exp ((a + b) * Real.log c) := by
      rw [Real.rpow_def_of_pos hc]
      field_simp
      <;> linarith
    calc
      a^(b + c) * b^(c + a) * c^(a + b) = Real.exp ((b + c) * Real.log a) * Real.exp ((c + a) * Real.log b) * Real.exp ((a + b) * Real.log c) := by rw [h6, h7, h8]
      _ = Real.exp (((b + c) * Real.log a) + (c + a) * Real.log b + (a + b) * Real.log c) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = Real.exp ((b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c) := by ring
  rw [h1, h5]
  have h2 : (2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c : ℝ) ≥ ( (b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c : ℝ) := by
    have h5 : (a - b) * (Real.log a - Real.log b) ≥ 0 := by
      by_cases h6 : a ≥ b
      ·
        have h7 : Real.log a ≥ Real.log b := by
          apply Real.log_le_log
          linarith
          linarith
        have h8 : (a - b : ℝ) ≥ 0 := by linarith
        have h9 : (Real.log a - Real.log b : ℝ) ≥ 0 := by linarith
        nlinarith
      ·
        have h7 : Real.log a ≤ Real.log b := by
          apply Real.log_le_log
          linarith
          linarith
        have h8 : (a - b : ℝ) ≤ 0 := by linarith
        have h9 : (Real.log a - Real.log b : ℝ) ≤ 0 := by linarith
        nlinarith
    have h5' : (b - c) * (Real.log b - Real.log c) ≥ 0 := by
      by_cases h6 : b ≥ c
      ·
        have h7 : Real.log b ≥ Real.log c := by
          apply Real.log_le_log
          linarith
          linarith
        have h8 : (b - c : ℝ) ≥ 0 := by linarith
        have h9 : (Real.log b - Real.log c : ℝ) ≥ 0 := by linarith
        nlinarith
      ·
        have h7 : Real.log b ≤ Real.log c := by
          apply Real.log_le_log
          linarith
          linarith
        have h8 : (b - c : ℝ) ≤ 0 := by linarith
        have h9 : (Real.log b - Real.log c : ℝ) ≤ 0 := by linarith
        nlinarith
    have h5'' : (c - a) * (Real.log c - Real.log a) ≥ 0 := by
      by_cases h6 : c ≥ a
      ·
        have h7 : Real.log c ≥ Real.log a := by
          apply Real.log_le_log
          linarith
          linarith
        have h8 : (c - a : ℝ) ≥ 0 := by linarith
        have h9 : (Real.log c - Real.log a : ℝ) ≥ 0 := by linarith
        nlinarith
      ·
        have h7 : Real.log c ≤ Real.log a := by
          apply Real.log_le_log
          linarith
          linarith
        have h8 : (c - a : ℝ) ≤ 0 := by linarith
        have h9 : (Real.log c - Real.log a : ℝ) ≤ 0 := by linarith
        nlinarith
    nlinarith
  have h3 : Real.exp (2 * a * Real.log a + 2 * b * Real.log b + 2 * c * Real.log c) ≥ Real.exp ((b + c) * Real.log a + (c + a) * Real.log b + (a + b) * Real.log c) := by
    apply Real.exp_le_exp_of_le
    linarith [h2]
  linarith [h3]