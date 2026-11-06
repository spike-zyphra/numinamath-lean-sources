import Mathlib

theorem inequalities_322843 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ a * b ^ b * c ^ c ≥ a ^ c * b ^ a * c ^ b := by

  have h3 : a ^ a * b ^ b * c ^ c = Real.exp (a * (Real.log a) + b * (Real.log b) + c * (Real.log c)) := by
    have h4 : a ^ a = Real.exp (a * (Real.log a)) := by
      rw [Real.rpow_def_of_pos ha]
      field_simp [ha.ne.symm]
      all_goals linarith
    have h5 : b ^ b = Real.exp (b * (Real.log b)) := by
      rw [Real.rpow_def_of_pos hb]
      field_simp [hb.ne.symm]
      all_goals linarith
    have h6 : c ^ c = Real.exp (c * (Real.log c)) := by
      rw [Real.rpow_def_of_pos hc]
      field_simp [hc.ne.symm]
      all_goals linarith
    have h7 : a ^ a * b ^ b * c ^ c = Real.exp (a * (Real.log a) + b * (Real.log b) + c * (Real.log c)) := by
      rw [h4, h5, h6]
      rw [← Real.exp_add, ← Real.exp_add]
      all_goals ring_nf
    linarith [h7]

  have h4 : a ^ c * b ^ a * c ^ b = Real.exp (c * (Real.log a) + a * (Real.log b) + b * (Real.log c)) := by
    have h5 : a ^ c = Real.exp (c * (Real.log a)) := by
      rw [Real.rpow_def_of_pos ha]
      field_simp [ha.ne.symm]
      all_goals linarith
    have h6 : b ^ a = Real.exp (a * (Real.log b)) := by
      rw [Real.rpow_def_of_pos hb]
      field_simp [hb.ne.symm]
      all_goals linarith
    have h7 : c ^ b = Real.exp (b * (Real.log c)) := by
      rw [Real.rpow_def_of_pos hc]
      field_simp [hc.ne.symm]
      all_goals linarith
    have h8 : a ^ c * b ^ a * c ^ b = Real.exp (c * (Real.log a) + a * (Real.log b) + b * (Real.log c)) := by
      rw [h5, h6, h7]
      rw [← Real.exp_add, ← Real.exp_add]
      all_goals ring_nf
    linarith [h8]

  have h5 : a * (Real.log a) + b * (Real.log b) + c * (Real.log c) ≥ c * (Real.log a) + a * (Real.log b) + b * (Real.log c) := by
    have h11 : a * (Real.log a) + b * (Real.log b) + c * (Real.log c) - (c * (Real.log a) + a * (Real.log b) + b * (Real.log c)) ≥ 0 := by
      have h12 : (a - c) * (Real.log a - Real.log c) ≥ 0 := by
        by_cases h51 : a ≥ c
        · -- If a ≥ c, then a - c ≥ 0 and log a ≥ log c
          have h21 : Real.log a ≥ Real.log c := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If a < c, then a - c < 0 and log a < log c
          have h21 : Real.log a < Real.log c := by
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h13 : (b - a) * (Real.log b - Real.log a) ≥ 0 := by
        by_cases h51 : b ≥ a
        · -- If b ≥ a, then b - a ≥ 0 and log b ≥ log a
          have h21 : Real.log b ≥ Real.log a := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If b < a, then b - a < 0 and log b < log a
          have h21 : Real.log b < Real.log a := by
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h14 : (c - b) * (Real.log c - Real.log b) ≥ 0 := by
        by_cases h51 : c ≥ b
        · -- If c ≥ b, then c - b ≥ 0 and log c ≥ log b
          have h21 : Real.log c ≥ Real.log b := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If c < b, then c - b < 0 and log c < log b
          have h21 : Real.log c < Real.log b := by
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h15 : (a - b) * (Real.log a - Real.log b) ≥ 0 := by
        by_cases h51 : a ≥ b
        · -- If a ≥ b, then a - b ≥ 0 and log a ≥ log b
          have h21 : Real.log a ≥ Real.log b := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If a < b, then a - b < 0 and log a < log b
          have h21 : Real.log a < Real.log b := by
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h16 : (b - c) * (Real.log b - Real.log c) ≥ 0 := by
        by_cases h51 : b ≥ c
        · -- If b ≥ c, then b - c ≥ 0 and log b ≥ log c
          have h21 : Real.log b ≥ Real.log c := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If b < c, then b - c < 0 and log b < log c
          have h21 : Real.log b < Real.log c := by
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h17 : (c - a) * (Real.log c - Real.log a) ≥ 0 := by
        by_cases h51 : c ≥ a
        · -- If c ≥ a, then c - a ≥ 0 and log c ≥ log a
          have h21 : Real.log c ≥ Real.log a := by
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- If c < a, then c - a < 0 and log c < log a
          have h21 : Real.log c < Real.log a := by
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (Real.log a - Real.log b), sq_nonneg (Real.log a - Real.log c), sq_nonneg (Real.log b - Real.log c),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
    linarith

  have h7 : Real.exp (a * (Real.log a) + b * (Real.log b) + c * (Real.log c)) ≥ Real.exp (c * (Real.log a) + a * (Real.log b) + b * (Real.log c)) := by
    apply Real.exp_le_exp_of_le
    linarith [h5]

  have h8 : a ^ a * b ^ b * c ^ c ≥ a ^ c * b ^ a * c ^ b := by
    have h11 : a ^ a * b ^ b * c ^ c = Real.exp (a * (Real.log a) + b * (Real.log b) + c * (Real.log c)) := h3
    have h12 : a ^ c * b ^ a * c ^ b = Real.exp (c * (Real.log a) + a * (Real.log b) + b * (Real.log c)) := h4
    rw [h11, h12]
    exact h7
  linarith [h8]