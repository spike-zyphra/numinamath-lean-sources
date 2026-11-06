import Mathlib

open Real

theorem algebra_209877 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 625) :
    logb (5 ^ ((1 : ℝ) / 3)) (a ^ 2) +
    logb (5 * sqrt 5) (125 * b ^ 9) +
    1 / logb (c ^ 2) (5 ^ ((1 : ℝ) / 3)) = 26 := by

  have h1 : logb (5 ^ ((1 : ℝ) / 3)) (a ^ 2) = (6 * (log a) / (log (5 : ℝ))) := by 
    have h2 : logb (5 ^ ((1 : ℝ) / 3)) (a ^ 2) = (log (a ^ 2)) / (log (5 ^ ((1 : ℝ) / 3))) := by 
      field_simp [logb]
    rw [h2]
    have h3 : log (a ^ 2) = 2 * log a := by 
      simp [log_pow]
    have h4 : log (5 ^ ((1 : ℝ) / 3)) = (1 / 3) * log (5 : ℝ) := by 
      rw [log_rpow]
      all_goals norm_num
    rw [h3, h4]
    field_simp
    <;> ring

  have h11 : logb (5 * sqrt 5) (125 * b ^ 9) = 2 * (log (5 : ℝ) + 3 * log b) / log (5 : ℝ) := by 
    have h12 : logb (5 * sqrt 5) (125 * b ^ 9) = (log (125 * b ^ 9)) / (log (5 * sqrt 5)) := by 
      field_simp [logb]
    have h13 : log (125 * b ^ 9) = log (125 : ℝ) + log (b ^ 9) := by 
      rw [log_mul (by norm_num) (by positivity)]
    have h14 : log (125 : ℝ) = 3 * log (5 : ℝ) := by 
      have h15 : (125 : ℝ) = (5 : ℝ) ^ 3 := by 
        norm_num
      rw [h15]
      simp [log_pow]
    have h15 : log (b ^ 9) = 9 * log b := by 
      simp [log_pow]
    have h16 : log (5 * sqrt 5) = log (5 : ℝ) + log (sqrt 5) := by 
      rw [log_mul (by norm_num) (by positivity)]
    have h17 : log (sqrt 5) = (1 / 2) * log (5 : ℝ) := by 
      have h18 : sqrt (5 : ℝ) = (5 : ℝ) ^ ((1 : ℝ) / 2) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h18]
      simp [log_rpow]
      all_goals norm_num
    rw [h12]
    rw [h13, h14, h15, h16, h17]
    field_simp
    <;> ring_nf

  have h12 : 1 / logb (c ^ 2) (5 ^ ((1 : ℝ) / 3)) = (6 * (log c) / (log (5 : ℝ))) := by 
    have h4 : logb (c ^ 2) (5 ^ ((1 : ℝ) / 3)) = (log (5 ^ ((1 : ℝ) / 3))) / (log (c ^ 2)) := by 
      field_simp [logb]
    have h5 : log (5 ^ ((1 : ℝ) / 3)) = (1 / 3) * log (5 : ℝ) := by 
      rw [log_rpow]
      all_goals norm_num
    have h6 : log (c ^ 2) = 2 * log c := by 
      simp [log_pow]
    have h4' : logb (c ^ 2) (5 ^ ((1 : ℝ) / 3)) = ((1 / 3) * log (5 : ℝ)) / (2 * log c) := by 
      rw [h4, h5, h6]
    rw [h4']
    field_simp
    <;> ring

  rw [h1, h11, h12]

  have h4 : log a + log b + log c = log (625 : ℝ) := by 
    calc 
      log a + log b + log c = log (a * b * c) := by 
        have h1 : log (a * b * c) = log (a * b) + log c := by 
          rw [show a * b * c = (a * b) * c by ring]
          rw [log_mul (by positivity) (by positivity)]
        have h2 : log (a * b) = log a + log b := by 
          rw [log_mul (by positivity) (by positivity)]
        linarith [h1, h2]
      _ = log (625 : ℝ) := by 
        rw [h]

  have h5 : log (625 : ℝ) = 4 * log (5 : ℝ) := by 
    have h6 : (625 : ℝ) = (5 : ℝ) ^ 4 := by 
      norm_num
    rw [h6]
    simp [log_pow]

  have h6' : log a + log b + log c = 4 * log (5 : ℝ) := by 
    linarith [h4, h5]

  have h7 : (6 * (log a) / (log (5 : ℝ)) ) + (2 * (log (5 : ℝ) + 3 * log b) / log (5 : ℝ) ) + (6 * (log c) / (log (5 : ℝ)) ) = 26 := by 
    have h8 : log (5 : ℝ) ≠ 0 := by positivity 
    have eq1 : (6 * (log a) / (log (5 : ℝ)) ) + (2 * (log (5 : ℝ) + 3 * log b) / log (5 : ℝ) ) + (6 * (log c) / (log (5 : ℝ)) ) = 
      (6 * log a + 2 * (log (5 : ℝ) + 3 * log b) + 6 * log c) / (log (5 : ℝ)) := by 
      field_simp [h8]
      <;> ring
    rw [eq1]
    have eq2 : 6 * log a + 2 * (log (5 : ℝ) + 3 * log b) + 6 * log c = 26 * log (5 : ℝ) := by 
      have eq3 : log a + log b + log c = 4 * log (5 : ℝ) := h6'
      have eq4 : 6 * log a + 2 * (log (5 : ℝ) + 3 * log b) + 6 * log c = 6 * (log a + log b + log c) + 2 * log (5 : ℝ) := by 
        ring_nf
      rw [eq4, eq3]
      linarith 
    rw [eq2] 
    field_simp [h8]
  linarith [h7]