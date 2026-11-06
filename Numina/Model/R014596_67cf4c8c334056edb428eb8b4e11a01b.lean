import Mathlib

theorem algebra_309780 {a b : ℝ} (ha : a = 2 * Real.sin (Real.pi / 4) + 1)
    (hb : b = 2 * Real.cos (Real.pi / 4) - 1) :
    ((a ^ 2 + b ^ 2) / (2 * a * b) - 1) / ((a ^ 2 - b ^ 2) / (a ^ 2 * b + a * b ^ 2)) = 1 := by

  have h1 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have h2 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four

  have ha' : a = Real.sqrt 2 + 1 := by
    rw [ha, h1]
    ring

  have hb' : b = Real.sqrt 2 - 1 := by
    rw [hb, h2]
    ring

  have hab : a * b = 1 := by
    rw [ha', hb']
    nlinarith [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ (2:ℝ) by norm_num)]

  have ha2 : a + b = 2 * Real.sqrt 2 := by
    rw [ha', hb']
    ring

  have ha3 : a - b = 2 := by
    rw [ha', hb']
    ring

  have ha4 : a^2 + b^2 = 6 := by
    rw [ha', hb']
    nlinarith [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ (2:ℝ) by norm_num)]

  have ha5 : a^2 - b^2 = 4 * Real.sqrt 2 := by
    calc
      a^2 - b^2 = (a - b) * (a + b) := by ring
      _ = 2 * (2 * Real.sqrt 2) := by rw [ha3, ha2]
      _ = 4 * Real.sqrt 2 := by ring

  have ha6 : a^2 * b + a * b^2 = 2 * Real.sqrt 2 := by
    calc
      a^2 * b + a * b^2 = a * b * (a + b) := by ring
      _ = 1 * (2 * Real.sqrt 2) := by rw [hab, ha2]
      _ = 2 * Real.sqrt 2 := by ring

  have h_num : (a ^ 2 + b ^ 2) / (2 * a * b) - 1 = 2 := by
    have h3 : 2 * a * b = 2 := by
      calc
        2 * a * b = 2 * (a * b) := by ring
        _ = 2 * 1 := by rw [hab]
        _ = (2 : ℝ) := by norm_num
    rw [h3, ha4]
    all_goals norm_num

  have h_den : (a ^ 2 - b ^ 2) / (a ^ 2 * b + a * b ^ 2) = 2 := by
    rw [ha5, ha6]
    have h4 : Real.sqrt 2 ≠ 0 := by
      positivity
    field_simp [h4]
    <;> ring_nf <;> field_simp [h4] <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  rw [h_num, h_den]
  all_goals norm_num