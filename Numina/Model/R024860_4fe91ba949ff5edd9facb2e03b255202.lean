import Mathlib


open Real Set

theorem algebra_172660 {x y : ℝ} (h₁ : Real.sin x + Real.sin y = (Real.sqrt 3 - 1) / 2)
    (h₂ : Real.cos x + Real.cos y = (Real.sqrt 3 + 1) / 2) :
    Real.cos (x + y) = Real.sqrt 3 / 2 := by

  have h3 : (Real.sin x + Real.sin y) ^ 2 + (Real.cos x + Real.cos y) ^ 2 = 2 := by
    have h4 : (Real.sin x + Real.sin y) ^ 2 + (Real.cos x + Real.cos y) ^ 2 =
        ((Real.sqrt 3 - 1) / 2) ^ 2 + ((Real.sqrt 3 + 1) / 2) ^ 2 := by
      rw [h₁, h₂]
    rw [h4]
    have h5 : ((Real.sqrt 3 - 1) / 2) ^ 2 + ((Real.sqrt 3 + 1) / 2) ^ 2 = 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    linarith

  have h4 : Real.sin x * Real.sin y + Real.cos x * Real.cos y = 0 := by
    have h5 : (Real.sin x + Real.sin y) ^ 2 + (Real.cos x + Real.cos y) ^ 2 =
        (Real.sin x ^ 2 + Real.cos x ^ 2) + (Real.sin y ^ 2 + Real.cos y ^ 2) + 2 * (Real.sin x * Real.sin y + Real.cos x * Real.cos y) := by
      nlinarith
    rw [show Real.sin x ^ 2 + Real.cos x ^ 2 = 1 by exact Real.sin_sq_add_cos_sq x] at h5
    rw [show Real.sin y ^ 2 + Real.cos y ^ 2 = 1 by exact Real.sin_sq_add_cos_sq y] at h5
    nlinarith [h3]

  have h5 : Real.cos (x + y) = 2 * (Real.cos ((x + y) / 2)) ^ 2 - 1 := by
    have h13 : Real.cos (x + y) = 2 * (Real.cos ((x + y) / 2)) ^ 2 - 1 := by
      have h17 : Real.cos (x + y) = 2 * (Real.cos ((x + y) / 2)) ^ 2 - 1 := by
        rw [←Real.cos_two_mul]
        all_goals ring_nf
      linarith
    linarith

  have h6 : Real.sin ((x + y) / 2) ^ 2 = (2 - Real.sqrt 3) / 4 := by
    have h8 : Real.sin x + Real.sin y = 2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) := by
      rw [show x = (x + y) / 2 + (x - y) / 2 by ring_nf, show y = (x + y) / 2 - (x - y) / 2 by ring_nf]
      rw [Real.sin_add, Real.sin_sub]
      ring
    rw [h₁] at h8

    have h9 : Real.cos x + Real.cos y = 2 * Real.cos ((x + y) / 2) * Real.cos ((x - y) / 2) := by
      rw [show x = (x + y) / 2 + (x - y) / 2 by ring_nf, show y = (x + y) / 2 - (x - y) / 2 by ring_nf]
      rw [Real.cos_add, Real.cos_sub]
      ring
    rw [h₂] at h9

    have h10 : Real.cos ((x - y) / 2) ^ 2 = 1 / 2 := by
      have h12 : Real.cos (x - y) = 0 := by
        have h11 : Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by
          rw [Real.cos_sub]
        have h14 : Real.cos x * Real.cos y + Real.sin x * Real.sin y = 0 := by nlinarith [h4]
        linarith
      have h13 : Real.cos (x - y) = 2 * Real.cos ((x - y) / 2) ^ 2 - 1 := by
        have h14 : Real.cos (x - y) = 2 * Real.cos ((x - y) / 2) ^ 2 - 1 := by
          rw [←Real.cos_two_mul]
          all_goals ring_nf
        linarith
      linarith

    have h30 : Real.sin ((x + y) / 2) ^ 2 + Real.cos ((x + y) / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq ((x + y) / 2)
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (Real.sqrt 3 ^ 2 - 3), Real.sqrt_nonneg 3]

  have h7 : Real.cos (x + y) = Real.sqrt 3 / 2 := by
    have h8 : Real.cos (x + y) = 1 - 2 * Real.sin ((x + y) / 2) ^ 2 := by
      have h17 : Real.cos (x + y) = 2 * (Real.cos ((x + y) / 2)) ^ 2 - 1 := h5
      have h14 : Real.sin ((x + y) / 2) ^ 2 + Real.cos ((x + y) / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq ((x + y) / 2)
      nlinarith
    rw [h8, h6]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]

  linarith