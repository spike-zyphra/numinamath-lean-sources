import Mathlib

theorem algebra_7872 (x y z : ℝ) (h₀ : (2 : ℝ)^x = 3) (h₁ : (2 : ℝ)^y = 7)
    (h₂ : (6 : ℝ)^z = 7) : z = y / (1 + x) := by
  have h3 : (6 : ℝ) ^ z = (2 * 3) ^ z := by norm_num
  have h4 : (2 * 3 : ℝ) ^ z = (2: ℝ) ^ z * (3: ℝ) ^ z := by 
    rw [show (2 * 3 : ℝ) = (2 : ℝ) * (3 : ℝ) by norm_num]
    rw [Real.mul_rpow]
    all_goals linarith
  have h5 : (3 : ℝ) ^ z = (2 : ℝ) ^ (x * z) := by 
    have h6 : (3 : ℝ) ^ z = ((2 : ℝ) ^ x) ^ z := by 
      rw [show (2 : ℝ) ^ x = (3 : ℝ) by linarith [h₀]]
      all_goals norm_num
    rw [h6]
    have h7 : ((2 : ℝ) ^ x) ^ z = (2 : ℝ) ^ (x * z) := by
      rw [← Real.rpow_mul]
      ring
      all_goals linarith
    rw [h7]
  have h6 : (6 : ℝ) ^ z = (2 : ℝ) ^ (z * (1 + x)) := by
    rw [h3, h4, h5]
    have h7 : (2 : ℝ) ^ z * (2 : ℝ) ^ (x * z) = (2 : ℝ) ^ (z + x * z) := by 
      rw [← Real.rpow_add]
      ring
      all_goals linarith
    have h8 : (2 : ℝ) ^ (z + x * z) = (2 : ℝ) ^ (z * (1 + x)) := by
      have h9 : z + x * z = z * (1 + x) := by
        ring
      rw [h9]
    rw [h7, h8]
  have h7 : (2 : ℝ) ^ (z * (1 + x)) = 7 := by 
    rw [← h6]
    linarith [h₂]
  have h8 : z * (1 + x) = y := by 
    have h9 : (2 : ℝ) ^ (z * (1 + x)) = (2 : ℝ) ^ y := by
      rw [h7]
      linarith [h₁]
    have h10 : z * (1 + x) = y := by
      apply_fun (Real.logb (2 : ℝ)) at h9
      have h11 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (z * (1 + x))) = Real.logb (2 : ℝ) ((2 : ℝ) ^ y) := by 
        linarith [h9]
      have h12 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (z * (1 + x))) = z * (1 + x) := by 
        rw [Real.logb_rpow]
        all_goals linarith
      have h13 : Real.logb (2 : ℝ) ((2 : ℝ) ^ y) = y := by 
        rw [Real.logb_rpow]
        all_goals linarith
      rw [h12, h13] at h11 
      linarith 
    linarith 
  have h12 : 1 + x ≠ 0 := by
    by_contra h
    have h13 : x = -1 := by 
      linarith 
    have h14 : (2 : ℝ) ^ x = 3 := h₀ 
    rw [h13] at h14 
    norm_num at h14 
    all_goals linarith 
  have h11 : z = y / (1 + x) := by 
    have h10 : z * (1 + x) = y := h8 
    have : z = y / (1 + x) := by 
      field_simp [show 1 + x ≠ 0 by exact h12]
      <;> nlinarith 
    exact_mod_cast this 
  exact h11