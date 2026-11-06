import Mathlib

theorem algebra_8555 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : a ^ (Real.logb 10 b) = 2) (h₂ : a ^ (Real.logb 10 a) * b ^ (Real.logb 10 b) = 5) :
    (a * b) ^ (Real.logb 10 (a * b)) = 20 := by

  have h3 : Real.logb 10 (a ^ (Real.logb 10 b)) = Real.logb 10 2 := by
    rw [h₁]

  have h4 : Real.logb 10 (a ^ (Real.logb 10 b)) = Real.logb 10 b * Real.logb 10 a := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  rw [h4] at h3

  have h5 : Real.logb 10 (a ^ (Real.logb 10 a) * b ^ (Real.logb 10 b)) = Real.logb 10 5 := by
    rw [h₂]

  have h6 : Real.logb 10 (a ^ (Real.logb 10 a) * b ^ (Real.logb 10 b)) =
      Real.logb 10 (a ^ (Real.logb 10 a)) + Real.logb 10 (b ^ (Real.logb 10 b)) := by
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h7 : Real.logb 10 (a ^ (Real.logb 10 a)) = Real.logb 10 a * Real.logb 10 a := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  have h8 : Real.logb 10 (b ^ (Real.logb 10 b)) = Real.logb 10 b * Real.logb 10 b := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  rw [h6, h7, h8] at h5

  have h8 : Real.logb 10 (a * b) = Real.logb 10 a + Real.logb 10 b := by
    rw [Real.logb_mul (by linarith) (by linarith)]

  have h9 : Real.logb 10 ((a * b) ^ (Real.logb 10 (a * b))) = Real.logb 10 (a * b) * Real.logb 10 (a * b) := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    positivity

  have h10 : Real.logb 10 (a * b) * Real.logb 10 (a * b) = Real.logb 10 20 := by
    have h11 : Real.logb 10 (a * b) = Real.logb 10 a + Real.logb 10 b := by
      rw [Real.logb_mul (by linarith) (by linarith)]
    rw [h11]
    have h12 : (Real.logb 10 a + Real.logb 10 b) ^ 2 = (Real.logb 10 a) ^ 2 + (Real.logb 10 b) ^ 2 + 2 * (Real.logb 10 a * Real.logb 10 b) := by
      ring
    have h13 : (Real.logb 10 a) ^ 2 + (Real.logb 10 b) ^ 2 = Real.logb 10 5 := by
      nlinarith [h5, h3]
    have h14 : (Real.logb 10 a * Real.logb 10 b) = Real.logb 10 2 := by
      nlinarith [h3]
    have h15 : (Real.logb 10 a + Real.logb 10 b) ^ 2 = Real.logb 10 5 + 2 * (Real.logb 10 2) := by
      nlinarith [h12, h13, h14]
    have h16 : Real.logb 10 20 = Real.logb 10 5 + 2 * (Real.logb 10 2) := by
      calc
        Real.logb 10 20 = Real.logb 10 (5 * 4) := by norm_num
        _ = Real.logb 10 5 + Real.logb 10 4 := by rw [Real.logb_mul (by norm_num) (by norm_num)]
        _ = Real.logb 10 5 + Real.logb 10 (2 ^ 2) := by norm_num
        _ = Real.logb 10 5 + 2 * (Real.logb 10 2) := by simp [Real.logb_pow]
        _ = Real.logb 10 5 + 2 * (Real.logb 10 2) := by ring
    nlinarith [h15, h16]

  have h18 : Real.logb 10 ((a * b) ^ (Real.logb 10 (a * b))) = Real.logb 10 20 := by
    rw [h9]
    linarith [h10]

  have h19 : (a * b) ^ (Real.logb 10 (a * b)) = 20 := by
    apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h18
  exact h19