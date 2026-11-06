import Mathlib

theorem algebra_187917 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : Real.logb 8 a + Real.logb 4 (b^2) = 5) (h₂ : Real.logb 8 b + Real.logb 4 (a^2) = 7) :
    a * b = 512 := by
  have h3 : Real.logb 4 (b^2) = 3 * Real.logb 8 b := by
    have h4 : Real.logb 4 (b^2) = Real.logb 8 (b^2) / Real.logb 8 (4 : ℝ) := by
      field_simp [Real.logb]
      all_goals
        try linarith
    have h5 : Real.logb 8 (4 : ℝ) = (2 / 3 : ℝ) := by
      rw [Real.logb]
      have h6 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
        calc
          Real.log (8 : ℝ) = Real.log (2 ^ 3) := by norm_num
          _ = 3 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      have h7 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
        calc
          Real.log (4 : ℝ) = Real.log (2 ^ 2) := by norm_num
          _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      field_simp [h6, h7]
      <;> ring_nf <;> norm_num
      all_goals linarith
    have h6 : Real.logb 8 (b^2 : ℝ) = 2 * Real.logb 8 b := by
      simp [Real.logb_pow]
      all_goals norm_num
    rw [h4, h5, h6]
    <;> field_simp <;> ring_nf <;> norm_num
    all_goals linarith

  have h7 : Real.logb 4 (a^2) = 3 * Real.logb 8 a := by
    have h8 : Real.logb 4 (a^2) = Real.logb 8 (a^2) / Real.logb 8 (4 : ℝ) := by
      field_simp [Real.logb]
      all_goals
        try linarith
    have h5 : Real.logb 8 (4 : ℝ) = (2 / 3 : ℝ) := by
      rw [Real.logb]
      have h6 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
        calc
          Real.log (8 : ℝ) = Real.log (2 ^ 3) := by norm_num
          _ = 3 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      have h7 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
        calc
          Real.log (4 : ℝ) = Real.log (2 ^ 2) := by norm_num
          _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      field_simp [h6, h7]
      <;> ring_nf <;> norm_num
      all_goals linarith
    have h6 : Real.logb 8 (a^2 : ℝ) = 2 * Real.logb 8 a := by
      simp [Real.logb_pow]
      all_goals norm_num
    rw [h8, h5, h6]
    <;> field_simp <;> ring_nf <;> norm_num
    all_goals linarith

  rw [h3] at h₁
  rw [h7] at h₂
  have eq3 : Real.logb 8 a = 2 := by
    linarith
  have eq4 : Real.logb 8 b = 1 := by
    linarith

  have ha8 : a = (8 : ℝ) ^ (Real.logb 8 a : ℝ) := by
    field_simp [Real.rpow_logb, show 0 < (8 : ℝ) by norm_num, show 0 < (a : ℝ) by linarith]
  rw [eq3] at ha8
  have ha64 : a = (8 : ℝ) ^ (2 : ℝ) := by
    linarith
  have hb8 : b = (8 : ℝ) ^ (Real.logb 8 b : ℝ) := by
    field_simp [Real.rpow_logb, show 0 < (8 : ℝ) by norm_num, show 0 < (b : ℝ) by linarith]
  rw [eq4] at hb8
  have hb64 : b = (8 : ℝ) ^ (1 : ℝ) := by
    linarith

  have ha64' : a = 64 := by
    rw [ha64]
    norm_num [Real.rpow_natCast]
  have hb8' : b = 8 := by
    rw [hb64]
    norm_num [Real.rpow_natCast]

  rw [ha64', hb8']
  all_goals norm_num