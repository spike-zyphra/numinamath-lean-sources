import Mathlib
open Real
theorem algebra_610548 (x : ℝ) (h : sin (1 + cos x ^ 2 + sin x ^ 4) = 13 / 14) : cos (1 + sin x ^ 2 + cos x ^ 4) = -3 * √3 / 14:= by

  have h1 : 1 + cos x ^ 2 + sin x ^ 4 = 1 + sin x ^ 2 + cos x ^ 4 := by
    have h2 : cos x ^ 2 = 1 - sin x ^ 2 := by
      have h7 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      linarith
    have h3 : sin x ^ 4 = (sin x ^ 2) ^ 2 := by ring
    rw [h3, h2]
    nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (sin x ^ 2 - 1 / 2)]

  have h2 : sin (1 + sin x ^ 2 + cos x ^ 4) = 13 / 14 := by
    rw [show 1 + sin x ^ 2 + cos x ^ 4 = 1 + cos x ^ 2 + sin x ^ 4 by linarith [h1]]
    linarith [h]

  have h3 : 1 + sin x ^ 2 + cos x ^ 4 ≥ 1.75 := by
    have h4 : 1 + sin x ^ 2 + cos x ^ 4 = 2 - sin x ^ 2 + (sin x ^ 2) ^ 2 := by
      have h5 : cos x ^ 4 = (1 - sin x ^ 2) ^ 2 := by
        have h6 : cos x ^ 2 = 1 - sin x ^ 2 := by
          have h7 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          nlinarith
        calc
          cos x ^ 4 = (cos x ^ 2) ^ 2 := by ring
          _ = (1 - sin x ^ 2) ^ 2 := by rw [h6]
      calc
        1 + sin x ^ 2 + cos x ^ 4 = 1 + sin x ^ 2 + (1 - sin x ^ 2) ^ 2 := by rw [h5]
        _ = 2 - sin x ^ 2 + (sin x ^ 2) ^ 2 := by nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2)]
    rw [h4]
    have h7 : sin x ^ 2 ≥ 0 := by
      positivity
    have h8 : sin x ^ 2 ≤ 1 := by
      have h9 : sin x ^ 2 ≤ 1 := by
        have h10 : -1 ≤ sin x ∧ sin x ≤ 1 := Real.sin_mem_Icc x
        nlinarith [sq_nonneg (sin x)]
      linarith
    nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2)]

  have h4 : 1 + sin x ^ 2 + cos x ^ 4 ≤ 2 := by
    have h4 : 1 + sin x ^ 2 + cos x ^ 4 = 2 - sin x ^ 2 + (sin x ^ 2) ^ 2 := by
      have h5 : cos x ^ 4 = (1 - sin x ^ 2) ^ 2 := by
        have h6 : cos x ^ 2 = 1 - sin x ^ 2 := by
          have h7 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          nlinarith
        calc
          cos x ^ 4 = (cos x ^ 2) ^ 2 := by ring
          _ = (1 - sin x ^ 2) ^ 2 := by rw [h6]
      calc
        1 + sin x ^ 2 + cos x ^ 4 = 1 + sin x ^ 2 + (1 - sin x ^ 2) ^ 2 := by rw [h5]
        _ = 2 - sin x ^ 2 + (sin x ^ 2) ^ 2 := by nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2)]
    rw [h4]
    have h7 : sin x ^ 2 ≥ 0 := by
      positivity
    have h8 : sin x ^ 2 ≤ 1 := by
      have h9 : sin x ^ 2 ≤ 1 := by
        have h10 : -1 ≤ sin x ∧ sin x ≤ 1 := Real.sin_mem_Icc x
        nlinarith [sq_nonneg (sin x)]
      linarith
    nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2)]

  have h5 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ^ 2 = 1 - Real.sin (1 + sin x ^ 2 + cos x ^ 4) ^ 2 := by
    have h8 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ^ 2 + Real.sin (1 + sin x ^ 2 + cos x ^ 4) ^ 2 = 1 := Real.cos_sq_add_sin_sq (1 + sin x ^ 2 + cos x ^ 4)
    nlinarith

  rw [h2] at h5
  have h6 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ^ 2 = 27 / 196 := by
    nlinarith

  have h7 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ≤ 0 := by
    have h8 : Real.pi / 2 ≤ 1 + sin x ^ 2 + cos x ^ 4 := by
      have h9 : 1 + sin x ^ 2 + cos x ^ 4 ≥ 1.75 := h3
      have h10 : Real.pi / 2 < (1.5708 : ℝ) := by linarith [Real.pi_lt_31416]
      have h11 : (1.5708 : ℝ) < 1 + sin x ^ 2 + cos x ^ 4 := by
        nlinarith
      linarith
    have h9 : 1 + sin x ^ 2 + cos x ^ 4 ≤ Real.pi := by
      have h10 : Real.pi > 3.1415 := by linarith [Real.pi_gt_31415]
      nlinarith
    have h11 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      all_goals linarith
    linarith

  have h8 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) = -3 * Real.sqrt 3 / 14 := by
    have h7' : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ≤ 0 := h7
    have h9 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ^ 2 = 27 / 196 := h6
    have h10 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) = - Real.sqrt (27 / 196) := by
      have h11 : Real.sqrt (Real.cos (1 + sin x ^ 2 + cos x ^ 4) ^ 2) = - Real.cos (1 + sin x ^ 2 + cos x ^ 4) := by
        have h13 : Real.cos (1 + sin x ^ 2 + cos x ^ 4) ≤ 0 := h7
        have h14 : Real.sqrt (Real.cos (1 + sin x ^ 2 + cos x ^ 4) ^ 2) = - Real.cos (1 + sin x ^ 2 + cos x ^ 4) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonpos h13]
          all_goals linarith
        linarith
      have h12 : Real.sqrt (Real.cos (1 + sin x ^ 2 + cos x ^ 4) ^ 2) = Real.sqrt (27 / 196) := by
        rw [h9]
      nlinarith
    have h13 : Real.sqrt (27 / 196 : ℝ) = (3 * Real.sqrt 3 / 14 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
    rw [h13] at h10
    nlinarith
  linarith