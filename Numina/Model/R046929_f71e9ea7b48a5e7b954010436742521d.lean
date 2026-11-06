import Mathlib

open Real
theorem algebra_318021 {a b c : ℝ} (ha : a = logb 8 5) (hb : b = logb 4 3)
    (hc : c = 2 / 3) : b > a ∧ a > c := by

  have ha2' : a = (logb 2 5) / 3 := by
    rw [ha]
    have h1 : Real.logb 8 5 = (logb 2 5) / (logb 2 8) := by
      field_simp [Real.logb]
    rw [h1]
    have h2 : logb 2 8 = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h2]

  have hb2' : b = (logb 2 3) / 2 := by
    rw [hb]
    have h1 : Real.logb 4 3 = (logb 2 3) / (logb 2 4) := by
      field_simp [Real.logb]
    rw [h1]
    have h2 : logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h2]

  have h1 : (logb 2 3) > 1 := by
    have h3 :  logb 2 3 > logb 2 2 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h4 : logb 2 2 = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith

  have h2 : (logb 2 5) > 2 := by
    have h3 :  logb 2 5 > logb 2 4 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h4 : logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith

  have h3 : 3 * (logb 2 3) > 2 * (logb 2 5) := by
    have h4 : logb 2 (3 ^ 3) = 3 * (logb 2 3) := by
      simp [logb_pow]
    have h5 : logb 2 (5 ^ 2) = 2 * (logb 2 5) := by
      simp [logb_pow]
    have h6 : logb 2 (3 ^ 3) > logb 2 (5 ^ 2) := by
      apply Real.logb_lt_logb
      all_goals norm_num
    linarith [h4, h5, h6]

  have h4 : b > a := by
    rw [hb2', ha2']
    linarith

  have h5 : a > c := by
    rw [ha2', hc]
    have h6 : (logb 2 5) > (2 : ℝ) := by
      have h3 :  logb 2 5 > logb 2 4 := by
        apply Real.logb_lt_logb
        all_goals norm_num
      have h4 : logb 2 4 = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith
    linarith

  constructor
  · -- $b > a$
    linarith
  · -- $a > c$
    linarith