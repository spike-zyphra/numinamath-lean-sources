import Mathlib

theorem algebra_15044 (x b : ℝ) (hb : 0 < b ∧ b ≠ 1)
  (h : (7 : ℝ) ^ (x + 7) = 8 ^ x) (hx: x = Real.logb b (7^7)) :
  b = 8 / 7 := by
  have h1 : 0 < b := hb.1
  have h2 : b ≠ 1 := hb.2

  have eq1 : (7 : ℝ) ^ (x + 7) = 8 ^ x := h

  have eq2 : Real.log ((7 : ℝ) ^ (x + 7)) = Real.log ((8 : ℝ) ^ x) := by 
    rw [eq1]

  have eq3 : Real.log ((7 : ℝ) ^ (x + 7)) = (x + 7) * Real.log (7 : ℝ) := by
    rw [Real.log_rpow]
    all_goals norm_num

  have eq4 : Real.log ((8 : ℝ) ^ x) = x * Real.log (8 : ℝ) := by
    rw [Real.log_rpow]
    all_goals norm_num

  rw [eq3, eq4] at eq2

  have eq5 : x * (Real.log (8 : ℝ) - Real.log (7 : ℝ)) = 7 * Real.log (7 : ℝ) := by
    nlinarith

  have eq6 : x = Real.logb b (7^7) := hx

  have eq7 : x = (7 * Real.log (7 : ℝ)) / Real.log (b : ℝ) := by
    rw [eq6]
    have h3 : Real.logb b (7^7 : ℝ) = (Real.log (7^7 : ℝ) ) / (Real.log (b : ℝ) ) := by
      field_simp [Real.logb]
    rw [h3]
    have h4 : Real.log (7^7 : ℝ) = 7 * Real.log (7 : ℝ) := by
      simp [Real.log_pow]
    rw [h4]

  have h11 : Real.log (b : ℝ) = Real.log (8 : ℝ) - Real.log (7 : ℝ) := by
    have h9' : x * (Real.log (8 : ℝ) - Real.log (7 : ℝ)) = 7 * Real.log (7 : ℝ) := eq5
    have h9'' : x = (7 * Real.log (7 : ℝ)) / Real.log (b : ℝ) := eq7
    rw [h9''] at h9'
    have h11 : Real.log (b : ℝ) ≠ 0 := by
      have h12 : b > 0 := by linarith
      have h13 : b ≠ 1 := h2
      exact Real.log_ne_zero_of_pos_of_ne_one h12 h13
    field_simp at h9' ⊢
    have h14 : Real.log (7 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals norm_num
    nlinarith

  have h13 : Real.log (b : ℝ) = Real.log (8 / 7 : ℝ) := by
    have h14 : Real.log (8 / 7 : ℝ) = Real.log (8 : ℝ) - Real.log (7 : ℝ) := by
      rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [h14, h11]

  have h14 : b = (8 / 7 : ℝ) := by
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr (by norm_num)) h13

  linarith