import Mathlib

theorem algebra_187289 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : Real.sqrt x + Real.sqrt y = 10) (h2 : x ^ ((1 : ℝ) / 4) + y ^ ((1 : ℝ) / 4) = 4) :
    (x = 1 ∧ y = 81) ∨ (x = 81 ∧ y = 1) := by
  have h3 : (x ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt x := by
    have h8 : (x ^ ((1 : ℝ) / 4)) ^ 2 = x ^ ((1 : ℝ) / 4 * (2 : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith [show x ≥ 0 by linarith]
    have h9 : (x ^ ((1 : ℝ) / 4 * (2 : ℝ)) ) = Real.sqrt x := by
      have h10 : x ^ ((1 : ℝ) / 4 * (2 : ℝ)) = x ^ ((1 : ℝ) / 2) := by
        ring_nf
      rw [h10]
      have h11 : x ^ ((1 : ℝ) / 2) = Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
      rw [h11]
    rw [h9] at h8
    exact h8
  have h4 : (y ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt y := by
    have h8 : (y ^ ((1 : ℝ) / 4)) ^ 2 = y ^ ((1 : ℝ) / 4 * (2 : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith [show y ≥ 0 by linarith]
    have h9 : (y ^ ((1 : ℝ) / 4 * (2 : ℝ)) ) = Real.sqrt y := by
      have h10 : y ^ ((1 : ℝ) / 4 * (2 : ℝ)) = y ^ ((1 : ℝ) / 2) := by
        ring_nf
      rw [h10]
      have h11 : y ^ ((1 : ℝ) / 2) = Real.sqrt y := by
        rw [Real.sqrt_eq_rpow]
      rw [h11]
    rw [h9] at h8
    exact h8
  have h6 : Real.sqrt x + Real.sqrt y = 10 := h1
  have h11 : x ^ ((1 : ℝ) / 4) + y ^ ((1 : ℝ) / 4) = 4 := h2
  have h12 : (x ^ ((1 : ℝ) / 4)) ^ 2 + (y ^ ((1 : ℝ) / 4)) ^ 2 = 10 := by
    nlinarith [h3, h4, h6, h11]
  have h13 : (x ^ ((1 : ℝ) / 4)) * (y ^ ((1 : ℝ) / 4)) = 3 := by
    nlinarith [h12, h11]
  have h14 : (x ^ ((1 : ℝ) / 4) - 1) * (x ^ ((1 : ℝ) / 4) - 3) = 0 := by
    nlinarith [h11, h13]
  cases (mul_eq_zero.mp h14) with
  | inl h15 =>
    have hx1 : x ^ ((1 : ℝ) / 4) = 1 := by
      linarith
    have hx_eq_1 : x = 1 := by
      have h16 : x ^ ((1 : ℝ) / 4) = 1 := hx1
      have h17 : x = (x ^ ((1 : ℝ) / 4)) ^ 4 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith [show x ≥ 0 by linarith]
      rw [h17, h16]
      norm_num
    have hy_eq_81 : y = 81 := by
      have h18 : y ^ ((1 : ℝ) / 4) = 3 := by
        linarith [h11, hx1]
      have h19 : y = (y ^ ((1 : ℝ) / 4)) ^ 4 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith [show y ≥ 0 by linarith]
      rw [h19, h18]
      norm_num
    left
    exact ⟨hx_eq_1, hy_eq_81⟩
  | inr h16 =>
    have hx1 : x ^ ((1 : ℝ) / 4) = 3 := by
      linarith
    have hx_eq_81 : x = 81 := by
      have h17 : x = (x ^ ((1 : ℝ) / 4)) ^ 4 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith [show x ≥ 0 by linarith]
      rw [h17, hx1]
      norm_num
    have hy_eq_1 : y = 1 := by
      have h18 : y ^ ((1 : ℝ) / 4) = 1 := by
        linarith [h11, hx1]
      have h19 : y = (y ^ ((1 : ℝ) / 4)) ^ 4 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith [show y ≥ 0 by linarith]
      rw [h19, h18]
      norm_num
    right
    exact ⟨hx_eq_81, hy_eq_1⟩