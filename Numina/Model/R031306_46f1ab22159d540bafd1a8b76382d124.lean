import Mathlib

open Real

theorem inequalities_118361 {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    a ^ (sqrt (logb a b)) + b ^ (sqrt (logb b a)) ≤ a + b := by 
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have ha1 : 0 < log a := by
    apply Real.log_pos
    linarith
  have hb1 : 0 < log b := by
    apply Real.log_pos
    linarith
  have h7 : logb a b = (log b) / (log a) := by
    field_simp [logb]
    all_goals linarith
  have h8 : logb b a = (log a) / (log b) := by 
    field_simp [logb]
    all_goals linarith
  have h9 : sqrt (logb a b) = sqrt ((log b) / (log a)) := by
    rw [h7]
  have h10 : sqrt (logb b a) = sqrt ((log a) / (log b)) := by 
    rw [h8]
  have h11 : a ^ (sqrt (logb a b)) = Real.exp (sqrt (log a * log b)) := by
    rw [show a ^ (sqrt (logb a b)) = Real.exp (log a * sqrt (logb a b)) by
      rw [Real.rpow_def_of_pos]
      field_simp [ha_pos]
      all_goals linarith
    ]
    rw [h9]
    have h12 : log a * sqrt ((log b) / (log a)) = sqrt (log a * log b) := by
      have h14 : sqrt ((log b) / (log a)) = sqrt (log b) / sqrt (log a) := by
        field_simp [Real.sqrt_div, ha1, hb1]
      rw [h14]
      field_simp [ha1, hb1, Real.sqrt_mul_self, mul_pos ha1 hb1]
      <;> ring_nf <;> field_simp [Real.sqrt_mul_self, ha1, hb1]
      <;> ring_nf <;> norm_num
    rw [h12]
  have h13 : b ^ (sqrt (logb b a)) = Real.exp (sqrt (log a * log b)) := by
    rw [show b ^ (sqrt (logb b a)) = Real.exp (log b * sqrt (logb b a)) by
      rw [Real.rpow_def_of_pos]
      field_simp [hb_pos]
      all_goals linarith
    ]
    rw [h10]
    have h14 : log b * sqrt ((log a) / (log b)) = sqrt (log a * log b) := by
      have h15 : sqrt ((log a) / (log b)) = sqrt (log a) / sqrt (log b) := by
        field_simp [Real.sqrt_div, ha1, hb1]
      rw [h15]
      field_simp [ha1, hb1, Real.sqrt_mul_self, mul_pos ha1 hb1]
      <;> ring_nf <;> field_simp [Real.sqrt_mul_self, ha1, hb1]
      <;> ring_nf <;> norm_num
    rw [h14]
  rw [h11, h13]
  have h14 : sqrt (log a * log b) ≥ 0 := by positivity
  have h17 : Real.exp (sqrt (log a * log b)) + Real.exp (sqrt (log a * log b)) ≤ Real.exp (log a) + Real.exp (log b) := by
    have h18 : Real.exp (sqrt (log a * log b)) + Real.exp (sqrt (log a * log b)) ≤ 2 * Real.exp ((log a + log b) / 2) := by
      have h19 : sqrt (log a * log b) ≤ (log a + log b) / 2 := by
        nlinarith [Real.sqrt_nonneg (log a * log b), Real.sq_sqrt (show 0 ≤ log a * log b by nlinarith), sq_nonneg (log a - log b), sq_nonneg (sqrt (log a * log b) - (log a + log b) / 2)]
      have h20 : Real.exp (sqrt (log a * log b)) ≤ Real.exp ((log a + log b) / 2) := by
        apply Real.exp_le_exp_of_le
        nlinarith [Real.sqrt_nonneg (log a * log b), h19]
      linarith [h20]
    have h15 : 2 * Real.exp ((log a + log b) / 2) ≤ Real.exp (log a) + Real.exp (log b) := by
      have h16 : Real.exp (log a) = a := by
        rw [Real.exp_log]
        linarith
      have h17 : Real.exp (log b) = b := by
        rw [Real.exp_log]
        linarith
      have h18 : Real.exp ((log a + log b) / 2) = Real.sqrt (Real.exp (log a) * Real.exp (log b)) := by
        have h19 : Real.exp ((log a + log b) / 2) = Real.sqrt (Real.exp (log a + log b)) := by
          have h20 : Real.exp ((log a + log b) / 2) = Real.sqrt (Real.exp (log a + log b)) := by
            rw [Real.sqrt_eq_rpow]
            rw [← Real.exp_mul]
            ring_nf
            <;> norm_num [Real.log_exp]
          exact h20
        have h20 : Real.exp (log a + log b) = Real.exp (log a) * Real.exp (log b) := by
          rw [Real.exp_add]
        rw [h20] at h19
        linarith [h19]
        all_goals nlinarith
        all_goals nlinarith
        all_goals nlinarith
      nlinarith [sq_nonneg (Real.exp ((log a + log b) / 2)), sq_nonneg (Real.exp (log a) - Real.exp (log b)), sq_nonneg (Real.sqrt (Real.exp (log a) * Real.exp (log b)) - Real.exp ((log a + log b) / 2)), 
          Real.sqrt_nonneg (Real.exp (log a) * Real.exp (log b)), Real.exp_nonneg (log a), Real.exp_nonneg (log b), 
          Real.sq_sqrt (show 0 ≤ Real.exp (log a) * Real.exp (log b) by positivity)]
    linarith [h15, h18]
  have h16 : Real.exp (log a) = a := by
    rw [Real.exp_log]
    linarith
  have h17 : Real.exp (log b) = b := by
    rw [Real.exp_log]
    linarith
  linarith [h16, h17, h17]