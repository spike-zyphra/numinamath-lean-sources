import Mathlib

theorem algebra_126361 {x : ℝ} (hx : x = 1 / Real.logb (1 / 2) (1 / 3) + 1 / Real.logb (1 / 5) (1 / 3)) :
    2 < x ∧ x < 3 := by

  have h1 : x = Real.logb 3 10 := by
    rw [hx]

    have h11 : Real.logb (1 / 2) (1 / 3) = Real.log 3 / Real.log 2 := by
      have h12 : Real.logb (1 / 2) (1 / 3) = Real.log (1 / 3) / Real.log (1 / 2) := by
        field_simp [Real.logb]
      have h13 : Real.log (1 / 3) = - Real.log 3 := by
        simp [Real.log_div, Real.log_one]
      have h14 : Real.log (1 / 2) = - Real.log 2 := by
        simp [Real.log_div, Real.log_one]
      rw [h12, h13, h14]
      <;> field_simp

    have h12 : Real.logb (1 / 5) (1 / 3) = Real.log 3 / Real.log 5 := by
      have h13 : Real.logb (1 / 5) (1 / 3) = Real.log (1 / 3) / Real.log (1 / 5) := by
        field_simp [Real.logb]
      have h14 : Real.log (1 / 3) = - Real.log 3 := by
        simp [Real.log_div, Real.log_one]
      have h15 : Real.log (1 / 5) = - Real.log 5 := by
        simp [Real.log_div, Real.log_one]
      rw [h13, h14, h15]
      <;> field_simp

    rw [h11, h12]

    have h13 : 1 / (Real.log 3 / Real.log 2) = Real.log 2 / Real.log 3 := by
      field_simp

    have h14 : 1 / (Real.log 3 / Real.log 5) = Real.log 5 / Real.log 3 := by
      field_simp

    rw [h13, h14]

    have h15 : Real.log 2 + Real.log 5 = Real.log 10 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      all_goals norm_num

    have h17 : Real.log 2 / Real.log 3 + Real.log 5 / Real.log 3 = (Real.log 10) / (Real.log 3) := by
      have h18 : Real.log 2 + Real.log 5 = Real.log 10 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        all_goals norm_num
      field_simp [(show Real.log 3 ≠ 0 by apply ne_of_gt; apply Real.log_pos; norm_num)]
      <;> linarith [h18]

    rw [h17]
    have h18 : (Real.log 10) / (Real.log 3) = Real.logb 3 10 := by
      field_simp [Real.logb]

    rw [h18]

  have h2 : 2 < Real.logb 3 10 := by
    have h31 : Real.logb 3 10 > 2 := by
      have h41 : Real.logb 3 9 = (2 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have h42 : Real.logb 3 10 > Real.logb 3 9 := by
        apply Real.logb_lt_logb
        all_goals norm_num
      linarith [h41, h42]
    linarith

  have h3 : Real.logb 3 10 < 3 := by
    have h32 : Real.logb 3 10 < (3 : ℝ) := by
      have h41 : Real.logb 3 27 = (3 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have h42 : Real.logb 3 10 < Real.logb 3 27 := by
        apply Real.logb_lt_logb
        all_goals norm_num
      linarith [h41, h42]
    linarith

  rw [h1]
  constructor <;> linarith [h2, h3]