import Mathlib

theorem algebra_283027 :
  {(x, y) : ℝ × ℝ | x > 0 ∧ y > 0 ∧ Real.sqrt (x * y) = 600 ∧ (x + y) / 2 = (2 * x * y) / (x + y) + 49} =
  {(800, 450), (450, 800)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is in the left side set, prove it is in the right side set
    rintro ⟨hx, hy, h1, h2⟩
    have h3 : x * y = 360000 := by
      have h4 : Real.sqrt (x * y) = 600 := h1
      have h5 : (Real.sqrt (x * y)) ^ 2 = (600 : ℝ) ^ 2 := by
        rw [h4]
      have h6 : (Real.sqrt (x * y)) ^ 2 = x * y := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith
    have h4 : x + y > 0 := by
      nlinarith
    have h5 : (x + y) ^ 2 - 98 * (x + y) - 1440000 = 0 := by
      have h6 : (x + y) / 2 = (2 * x * y) / (x + y) + 49 := h2
      rw [show 2 * x * y = 720000 by nlinarith [h3]] at h6
      field_simp [(show x + y ≠ 0 by positivity)] at h6
      nlinarith [h6, h3]
    have h6 : (x + y - 1250) * (x + y + 1152) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Case x + y - 1250 = 0, so x + y = 1250
      have hS : x + y = 1250 := by linarith
      have h10 : x ^ 2 - 1250 * x + 360000 = 0 := by
        have h11 : x + y = 1250 := by linarith [hS]
        have h13 : y = 1250 - x := by linarith
        rw [h13] at h3
        nlinarith
      have h11 : (x - 800) * (x - 450) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h11) with h12 h13
      · -- Case x - 800 = 0, so x = 800
        have hx1 : x = 800 := by linarith
        have hy1 : y = 450 := by
          nlinarith
        simp [hx1, hy1]
      · -- Case x - 450 = 0, so x = 450
        have hx2 : x = 450 := by linarith
        have hy2 : y = 800 := by
          nlinarith
        simp [hx2, hy2]
    · -- Case x + y + 1152 = 0, so x + y = -1152
      have hS : x + y = -1152 := by linarith
      nlinarith
  · -- Show that (800, 450) and (450, 800) satisfy the conditions
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Show (800, 450) in the left side set
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · -- Show sqrt (800 * 450) = 600
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- Show (800 + 450)/2 = (2 * 800 * 450)/(800 + 450) + 49
        norm_num
    · -- Show (450, 800) in the left side set
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · -- Show sqrt (450 * 800) = 600
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- Show (450 + 800)/2 = (2 * 450 * 800)/(450 + 800) + 49
        norm_num