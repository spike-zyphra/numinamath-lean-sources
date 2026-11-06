import Mathlib

theorem algebra_95267 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : a ^ b = b ^ a)
    (h2 : b = 9 * a) : a = 3 ^ ((1 : ℝ) / 4) := by
  rw [show b = 9 * a by linarith [h2]] at h1
  have h3 : a ^ (9 * a : ℝ) = (9 * a : ℝ) ^ a := by
    simpa using h1
  have h4 : 0 < a := ha
  have h5 : 0 < (9 * a : ℝ) := by nlinarith
  have h6 : a ^ (9 * a : ℝ) = (9 * a : ℝ) ^ a := h3
  have h7 : 9 * a * (Real.log a) = a * (Real.log (9 * a : ℝ)) := by
    have h8 : Real.log ((a ^ (9 * a : ℝ) ) ) = Real.log (( (9 * a : ℝ) ^ a ) ) := by
      rw [h6]
    have h9 : Real.log ((a ^ (9 * a : ℝ) ) ) = 9 * a * Real.log a := by
      rw [Real.log_rpow]
      all_goals nlinarith
    have h10 : Real.log (( (9 * a : ℝ) ^ a ) ) = a * Real.log (9 * a : ℝ) := by
      rw [Real.log_rpow]
      all_goals nlinarith
    linarith [h8, h9, h10]
  have h10 : 9 * a * (Real.log a) = a * (Real.log (9 * a : ℝ)) := h7
  have h11 : 9 * (Real.log a) = Real.log (9 * a : ℝ) := by
    have ha' : a > 0 := by linarith
    apply (mul_left_inj' (ne_of_gt ha')).mp
    linarith
  have h12 : Real.log (9 * a : ℝ) = Real.log (9 : ℝ) + Real.log (a : ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  rw [h12] at h11
  have h13 : 8 * (Real.log a) = Real.log (9 : ℝ) := by
    nlinarith
  have h14 : Real.log (9 : ℝ) = 2 * Real.log (3 : ℝ) := by
    calc
      Real.log (9 : ℝ) = Real.log ((3 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
  rw [h14] at h13
  have h15 : 4 * (Real.log a) = Real.log (3 : ℝ) := by
    linarith
  have h16 : Real.log (a ^ 4 : ℝ) = Real.log (3 : ℝ) := by
    have h17 : Real.log (a ^ 4 : ℝ) = 4 * (Real.log a : ℝ) := by
      simp [Real.log_pow]
    linarith [h17, h15]
  have h17 : a ^ 4 = (3 : ℝ) := by
    have h18 : a ^ 4 > 0 := by positivity
    have h19 : (3 : ℝ) > 0 := by norm_num
    have h20 : Real.log (a ^ 4 : ℝ) = Real.log (3 : ℝ) := h16
    have h21 : a ^ 4 = (3 : ℝ) := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h18) (Set.mem_Ioi.mpr h19) h20
    linarith
  have h18 : a = (3 : ℝ) ^ ((1 : ℝ) / 4) := by
    have h19 : a ^ 4 = (3 : ℝ) := h17
    have h20 : a = ((a ^ 4 : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals positivity
    rw [h19] at h20
    linarith
  linarith