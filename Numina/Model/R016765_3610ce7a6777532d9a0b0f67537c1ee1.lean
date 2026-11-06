import Mathlib

theorem algebra_167565 (x : ℝ) (hx : x > 0) :
    x * Real.logb (x + 1) 5 * Real.logb (1 / 5 ^ ((1 : ℝ) / 3)) (x + 1) = (x - 4) / x ↔ x = 1 := by
  constructor
  · -- Assume left side, prove x = 1
    intro h_eq
    have h1 : x > 0 := hx
    have h2 : x + 1 > 1 := by linarith
    have h3 : (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (5 : ℝ) ^ (-1 / 3 : ℝ) := by 
      rw [show (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (5 : ℝ) ^ (-1 / 3 : ℝ) by
        rw [show (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (5 ^ (1 / 3 : ℝ))⁻¹ by field_simp]
        rw [← Real.rpow_neg]
        ring_nf
        all_goals linarith
      ]
    have h4 : Real.log (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (-1 / 3 : ℝ) * Real.log 5 := by 
      rw [h3]
      have h5 : Real.log ((5 : ℝ) ^ (-1 / 3 : ℝ)) = (-1 / 3 : ℝ) * Real.log (5 : ℝ) := by
        rw [Real.log_rpow]
        all_goals linarith
      linarith [h5]
    have h5 : Real.logb (x + 1) 5 = Real.log 5 / Real.log (x + 1) := by 
      field_simp [Real.logb]
    have h6 : Real.logb (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) (x + 1) = Real.log (x + 1) / Real.log (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) := by 
      field_simp [Real.logb]
    rw [h5] at h_eq
    rw [h6] at h_eq
    rw [h4] at h_eq
    have h7 : x * (Real.log 5 / Real.log (x + 1)) * (Real.log (x + 1) / ((-1 / 3 : ℝ) * Real.log 5)) = -3 * x := by
      have hx1 : Real.log (x + 1) ≠ 0 := by
        have hx1' : x + 1 > 1 := by linarith
        have : Real.log (x + 1) > 0 := by
          apply Real.log_pos
          linarith
        linarith
      have hx2 : Real.log 5 > 0 := by
        apply Real.log_pos
        norm_num
      field_simp [hx1, hx2]
      <;> ring_nf
    have h8 : -3 * x = (x - 4) / x := by
      have h7' : x * (Real.log 5 / Real.log (x + 1)) * (Real.log (x + 1) / ((-1 / 3 : ℝ) * Real.log 5)) = -3 * x := h7
      linarith [h_eq, h7']
    have h9 : -3 * x ^ 2 = x - 4 := by
      have h10 : x > 0 := hx
      have h11 : x ≠ 0 := by linarith
      have h12 : -3 * x = (x - 4) / x := h8
      have h13 : x * (-3 * x) = x * ((x - 4) / x) := by
        rw [h12]
      have h14 : x * ((x - 4) / x) = x - 4 := by
        field_simp [show x ≠ 0 by linarith]
      nlinarith [h13, h14]
    have h10 : 3 * x ^ 2 + x - 4 = 0 := by nlinarith [h9]
    have h11 : (x - 1) * (3 * x + 4) = 0 := by
      nlinarith [h10]
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- Case x - 1 = 0, so x = 1
      linarith
    · -- Case 3 * x + 4 = 0, so x = -4/3
      nlinarith [show x > 0 from hx]
  · -- Assume x = 1, prove the equation
    intro h_eq
    rw [h_eq]
    have h3 : (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (5 : ℝ) ^ (-1 / 3 : ℝ) := by
      rw [show (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (5 : ℝ) ^ (-1 / 3 : ℝ) by
        rw [show (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (5 ^ (1 / 3 : ℝ))⁻¹ by field_simp]
        rw [← Real.rpow_neg]
        ring_nf
        all_goals linarith
      ]
    have h4 : Real.log (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) = (-1 / 3 : ℝ) * Real.log 5 := by 
      rw [h3]
      have h5 : Real.log ((5 : ℝ) ^ (-1 / 3 : ℝ)) = (-1 / 3 : ℝ) * Real.log (5 : ℝ) := by
        rw [Real.log_rpow]
        all_goals linarith
      linarith [h5]
    have h5 : Real.logb (1 + 1 : ℝ) (5 : ℝ) = Real.log 5 / Real.log (1 + 1 : ℝ) := by 
      field_simp [Real.logb]
    have h6 : Real.logb (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) (1 + 1 : ℝ) = Real.log (1 + 1 : ℝ) / Real.log (1 / (5 : ℝ) ^ ((1 : ℝ) / 3)) := by 
      field_simp [Real.logb]
    rw [h5, h6, h4]
    have h7 : (Real.log 5 / Real.log (1 + 1 : ℝ)) * (Real.log (1 + 1 : ℝ) / ((-1 / 3 : ℝ) * Real.log 5)) = -3 := by
      have h8 : Real.log (1 + 1 : ℝ) > 0 := by
        have h2' : (1 + 1 : ℝ) > 1 := by norm_num
        have : Real.log (1 + 1 : ℝ) > 0 := by
          apply Real.log_pos
          linarith
        linarith
      have h9 : Real.log 5 > 0 := by
        apply Real.log_pos
        norm_num
      field_simp [h8, h9]
      <;> ring_nf
    field_simp [h7]
    <;> norm_num
    all_goals linarith