import Mathlib

open Real

theorem inequalities_275517 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 ≤ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) := by
  have hb_eq : b = 2 - a := by linarith [h]

  have h1 : 0 < b := hb
  have h2 : a ^ n * b ^ n ≤ (1 : ℝ) := by
    have h3 : a * b ≤ (1 : ℝ) := by
      have h4 : b = 2 - a := by linarith
      rw [h4]
      nlinarith [sq_nonneg (a - 1)]
    have h4 : a ^ n * b ^ n = (a * b) ^ n := by
      rw [mul_pow]
    rw [h4]
    have h5 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
      apply pow_le_pow_left
      all_goals
        nlinarith [h3]
      all_goals
        nlinarith [h3]
    have h6 : (1 : ℝ) ^ n = 1 := by
      simp
    linarith [h5, h6]
    
  have h3 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 ≥ 0 := by
    have h_pos1 : 0 < 1 + a ^ n := by
      positivity
    have h_pos2 : 0 < 1 + b ^ n := by
      positivity

    have h4 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 =
      (1 - a ^ n * b ^ n) / ((1 + a ^ n) * (1 + b ^ n)) := by
      field_simp
      <;> ring
    rw [h4]
    apply div_nonneg
    -- Show that 1 - a^n * b^n ≥ 0
    nlinarith [h2]

    -- Show that (1 + a^n) * (1 + b^n) > 0
    positivity
  
  linarith [h3]
  all_goals nlinarith [Real.rpow_pos_of_pos ha n, Real.rpow_pos_of_pos hb n]
  all_goals nlinarith [Real.rpow_pos_of_pos ha n, Real.rpow_pos_of_pos hb n]