import Mathlib

theorem algebra_21335 {x : ℝ} (hx : 0 < x) (hx1 : x * Real.sqrt 3 + Real.sqrt 2 ≠ 0) (h : Real.sqrt x / (x * Real.sqrt 3 + Real.sqrt 2) = 1 / (2 * x * Real.sqrt 6 + 4)) :
    x = 1 / 8 := by
  have h1 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    calc 
      Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
      _ = Real.sqrt 2 * Real.sqrt 3 := by 
        rw [Real.sqrt_mul (by norm_num)]
  have h2 : (2 * x * Real.sqrt 6 + 4) = 2 * Real.sqrt 2 * (x * Real.sqrt 3 + Real.sqrt 2) := by 
    rw [h1]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)]
  rw [h2] at h
  have h3 : Real.sqrt x / (x * Real.sqrt 3 + Real.sqrt 2) = 1 / (2 * Real.sqrt 2 * (x * Real.sqrt 3 + Real.sqrt 2)) := by 
    simpa using h
  have h4 : Real.sqrt x * (2 * Real.sqrt 2 * (x * Real.sqrt 3 + Real.sqrt 2)) = (x * Real.sqrt 3 + Real.sqrt 2) := by
    have h5 : Real.sqrt x / (x * Real.sqrt 3 + Real.sqrt 2) = 1 / (2 * Real.sqrt 2 * (x * Real.sqrt 3 + Real.sqrt 2)) := h3
    have h6 : (x * Real.sqrt 3 + Real.sqrt 2) ≠ 0 := by
      exact hx1
    have h7 : (2 * Real.sqrt 2 * (x * Real.sqrt 3 + Real.sqrt 2)) ≠ 0 := by
      intro h8
      apply hx1
      have : (x * Real.sqrt 3 + Real.sqrt 2) = 0 := by
        nlinarith [show Real.sqrt 2 > 0 by positivity, h8]
      assumption
    field_simp [h6, h7] at h5 ⊢
    <;> nlinarith [h5, Real.sqrt_pos.mpr (show x > 0 by linarith)]
  have h8 : x * Real.sqrt 3 + Real.sqrt 2 ≠ 0 := hx1
  have h9 : Real.sqrt x * (2 * Real.sqrt 2) = 1 := by 
    apply (mul_left_inj' h8).mp 
    linarith 
  have h10 : Real.sqrt x = 1 / (2 * Real.sqrt 2) := by 
    field_simp at h9 ⊢ 
    linarith 
  have h11 : Real.sqrt x = Real.sqrt 2 / 4 := by 
    rw [h10] 
    field_simp 
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h12 : x = 1 / 8 := by
    calc 
      x = (Real.sqrt x) ^ 2 := by 
        rw [Real.sq_sqrt] 
        linarith 
      _ = (Real.sqrt 2 / 4) ^ 2 := by 
        rw [h11] 
      _ = (Real.sqrt 2 ^ 2) / 16 := by 
        ring_nf 
      _ = (2) / 16 := by 
        rw [Real.sq_sqrt (by norm_num)]
      _ = 1 / 8 := by 
        norm_num
  exact h12