import Mathlib

theorem algebra_14014 {f : ℝ → ℝ} (hf : ∀ x, 0 < x → f x = Real.cos x + Real.logb 2 x)
    (a : ℝ) (ha : 0 < a) (h : f a = f (2 * a)) :
    f (2 * a) - f (4 * a) = -3 ∨ f (2 * a) - f (4 * a) = -1 := by
  have h1 : f a = Real.cos a + Real.logb 2 a := hf a ha
  have h2a_pos : 0 < 2 * a := by linarith
  have h2 : f (2 * a) = Real.cos (2 * a) + Real.logb 2 (2 * a) := hf (2 * a) h2a_pos
  rw [h1, h2] at h
  have h3 : Real.logb 2 (2 * a) = 1 + Real.logb 2 a := by
    have h4 : Real.logb 2 (2 * a) = Real.logb 2 (2 : ℝ) + Real.logb 2 a := by
      rw [Real.logb_mul (by linarith) (by linarith)]
    have h5 : Real.logb 2 (2 : ℝ) = 1 := by
      norm_num [Real.logb_eq_iff_rpow_eq]
    linarith [h4, h5]
  rw [h3] at h
  have eq1 : Real.cos a - Real.cos (2 * a) = 1 := by linarith
  have eq2 : Real.cos (2 * a) = 2 * Real.cos a ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have eq3 : Real.cos a * (1 - 2 * Real.cos a) = 0 := by
    rw [eq2] at eq1
    nlinarith
  cases' (mul_eq_zero.mp eq3) with hcos hcos1
  · -- $\cos a = 0$ 
    have hcos1 : Real.cos a = 0 := hcos
    have hcos2a : Real.cos (2 * a) = -1 := by
      have h1 : Real.cos (2 * a) = 2 * Real.cos a ^ 2 - 1 := by
        rw [Real.cos_two_mul]
      rw [h1, hcos1]
      norm_num
    have hcos4a : Real.cos (4 * a) = 1 := by
      have h1 : Real.cos (4 * a) = 2 * Real.cos (2 * a) ^ 2 - 1 := by
        have h2 : 4 * a = 2 * (2 * a) := by ring
        rw [h2]
        rw [Real.cos_two_mul]
      rw [h1, hcos2a]
      norm_num
    have h4a1 : f (2 * a) - f (4 * a) = -3 := by
      have h4a5 : f (2 * a) = Real.cos (2 * a) + Real.logb 2 (2 * a) := hf (2 * a) h2a_pos
      have h4a6 : f (4 * a) = Real.cos (4 * a) + Real.logb 2 (4 * a) := hf (4 * a) (by nlinarith)
      rw [h4a5, h4a6]
      have h4a3 : Real.logb 2 (2 * a) = 1 + Real.logb 2 a := h3
      have h4a4 : Real.logb 2 (4 * a) = 2 + Real.logb 2 a := by
        have h5 : 0 < 4 * a := by nlinarith
        have h6 : Real.logb 2 (4 * a) = Real.logb 2 (4 : ℝ) + Real.logb 2 a := by
          rw [Real.logb_mul (by nlinarith) (by nlinarith)]
        have h7 : Real.logb 2 (4 : ℝ) = 2 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith [h6, h7]
      rw [h4a3, h4a4, hcos2a, hcos4a]
      nlinarith
    left
    linarith [h4a1]
  · -- $1 - 2\cos a = 0$ 
    have hcos2 : Real.cos a = 1 / 2 := by 
      linarith
    have hcos2a : Real.cos (2 * a) = -1 / 2 := by
      have eq4 : Real.cos (2 * a) = 2 * Real.cos a ^ 2 - 1 := by
        rw [Real.cos_two_mul]
      rw [eq4, hcos2]
      norm_num
    have hcos4a : Real.cos (4 * a) = -1 / 2 := by
      have eq5 : Real.cos (4 * a) = 2 * Real.cos (2 * a) ^ 2 - 1 := by
        have h1 : 4 * a = 2 * (2 * a) := by ring
        rw [h1]
        rw [Real.cos_two_mul]
      rw [eq5, hcos2a]
      norm_num
    have h4a1 : f (2 * a) - f (4 * a) = -1 := by
      have h4a5 : f (2 * a) = Real.cos (2 * a) + Real.logb 2 (2 * a) := hf (2 * a) h2a_pos
      have h4a6 : f (4 * a) = Real.cos (4 * a) + Real.logb 2 (4 * a) := hf (4 * a) (by nlinarith)
      rw [h4a5, h4a6]
      have h4a3 : Real.logb 2 (2 * a) = 1 + Real.logb 2 a := h3
      have h4a4 : Real.logb 2 (4 * a) = 2 + Real.logb 2 a := by
        have h5 : 0 < 4 * a := by nlinarith
        have h6 : Real.logb 2 (4 * a) = Real.logb 2 (4 : ℝ) + Real.logb 2 a := by
          rw [Real.logb_mul (by nlinarith) (by nlinarith)]
        have h7 : Real.logb 2 (4 : ℝ) = 2 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith [h6, h7]
      rw [h4a3, h4a4, hcos2a, hcos4a]
      nlinarith
    right
    linarith [h4a1]