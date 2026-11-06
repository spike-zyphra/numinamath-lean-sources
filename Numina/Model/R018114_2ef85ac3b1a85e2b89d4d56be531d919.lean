import Mathlib

open Real Set

theorem algebra_290485 {x : ℝ} (h : arccos (4/5) - arccos (-4/5) = arcsin x) :
    False := by

  have h1 : -(Real.pi / 2) ≤ arcsin x := by 
    linarith [Real.neg_pi_div_two_le_arcsin x]

  have h2 : arcsin x ≤ Real.pi / 2 := by 
    linarith [Real.arcsin_le_pi_div_two x]

  have h3 : -(Real.pi / 2) ≤ arccos (4/5) - arccos (-4/5) := by 
    linarith [h, h1]

  have h4 : arccos (4/5) - arccos (-4/5) ≤ Real.pi / 2 := by 
    linarith [h, h2]

  have h5 : cos (arccos (4/5) - arccos (-4/5)) ≥ 0 := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    all_goals linarith [h3, h4]

  have h6 : cos (arccos (4/5) - arccos (-4/5)) = -7/25 := by
    have h7 : cos (arccos (4 / 5)) = 4 / 5 := by
      rw [Real.cos_arccos]
      all_goals norm_num
    have h8 : cos (arccos (-4 / 5)) = -4 / 5 := by
      rw [Real.cos_arccos]
      all_goals norm_num
    have h9 : sin (arccos (4 / 5)) = 3 / 5 := by
      have h11 : sin (arccos (4 / 5)) = Real.sqrt (1 - (4 / 5) ^ 2) := by
        rw [Real.sin_arccos]
      rw [h11]
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> linarith
    have h10 : sin (arccos (-4 / 5)) = 3 / 5 := by
      have h11 : sin (arccos (-4 / 5)) = Real.sqrt (1 - (-4 / 5) ^ 2) := by
        rw [Real.sin_arccos]
      rw [h11]
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> linarith
    rw [Real.cos_sub]
    rw [h7, h8, h9, h10]
    norm_num

  linarith [h5, h6]