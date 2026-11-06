import Mathlib

theorem algebra_247629 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hf : ∀ x ∈ Set.Ioo 0 1, f x = 2 ^ x) (hf' : ∀ x, f (x + 2) = f x) :
    f (Real.logb (1 / 2) 23) = -23 / 16 := by 
  have h1 : Real.logb (1 / 2) 23 = - Real.logb 2 23 := by 
    have h2 : Real.logb (1 / 2) 23 = Real.logb 2 23 / Real.logb 2 (1 / 2) := by 
      field_simp [Real.logb]
    have h3 : Real.logb 2 (1 / 2) = -1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h2, h3]
    all_goals ring
  have h2 : f (Real.logb (1 / 2) 23) = - f (Real.logb 2 23) := by
    rw [h1]
    rw [hodd (Real.logb 2 23)]
    all_goals linarith
  have h3 : Real.logb 2 23 > 4 := by 
    have h1 : Real.logb 2 23 > Real.logb 2 16 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h2 : Real.logb 2 16 = 4 := by 
      calc 
        Real.logb 2 16 = Real.logb 2 (2 ^ 4 : ℝ) := by norm_num
        _ = 4 := by 
          simp [Real.logb_pow]
    linarith
  have h4 : Real.logb 2 23 < 5 := by 
    have h1 : Real.logb 2 23 < Real.logb 2 32 := by 
      apply Real.logb_lt_logb
      all_goals norm_num
    have h2 : Real.logb 2 32 = 5 := by 
      calc 
        Real.logb 2 32 = Real.logb 2 (2 ^ 5 : ℝ) := by norm_num
        _ = 5 := by 
          simp [Real.logb_pow]
    linarith
  have h5 : f (Real.logb 2 23) = f (Real.logb 2 23 - 4) := by 
    have h6 : f (Real.logb 2 23 - 4 + 4) = f (Real.logb 2 23 - 4) := by 
      have h7 : f (Real.logb 2 23 - 4 + 2) = f (Real.logb 2 23 - 4) := by 
        apply hf'
      have h8 : f (Real.logb 2 23 - 4 + 4) = f (Real.logb 2 23 - 4 + 2) := by 
        have h9 : f (Real.logb 2 23 - 4 + 2) = f (Real.logb 2 23 - 4 + 2) := by rfl
        have h10 : f ((Real.logb 2 23 - 4 + 2) + 2) = f (Real.logb 2 23 - 4 + 2) := by
          rw [show (Real.logb 2 23 - 4 + 2) + 2 = (Real.logb 2 23 - 4 + 2) + 2 by ring]
          apply hf'
        have : (Real.logb 2 23 - 4 + 2) + 2 = Real.logb 2 23 - 4 + 4 := by ring
        rw [this] at h10
        linarith
      rw [h8, h7]
    have h7 : Real.logb 2 23 - 4 + 4 = Real.logb 2 23 := by ring
    rw [h7] at h6
    linarith
  have h8 : Real.logb 2 23 - 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor 
    · 
      linarith
    · 
      linarith
  have h9 : f (Real.logb 2 23 - 4) = (23 / 16 : ℝ) := by 
    specialize hf (Real.logb 2 23 - 4) h8
    rw [hf]
    have : (2 : ℝ) ^ (Real.logb 2 23 - 4 : ℝ) = (23 / 16 : ℝ) := by 
      have h7 : (23 : ℝ) / 16 = (23 / 16 : ℝ) := by norm_num
      have h8 : (2 : ℝ) ^ (Real.logb 2 23 - 4 : ℝ) = (2 : ℝ) ^ (Real.logb 2 (23 / 16 : ℝ) : ℝ) := by 
        have h9 : Real.logb 2 (23 / 16 : ℝ) = Real.logb 2 23 - 4 := by 
          have h2 : Real.logb 2 (23 / 16 : ℝ) = Real.logb 2 (23 : ℝ) - Real.logb 2 (16 : ℝ) := by 
            rw [Real.logb_div (by linarith) (by linarith)]
          have h10 : Real.logb 2 (16 : ℝ) = (4 : ℝ) := by
            have h11 : Real.logb 2 (16 : ℝ) = (4 : ℝ) := by
              rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
            linarith
          linarith
        rw [h9]
        all_goals linarith
      rw [h8]
      rw [Real.rpow_logb]
      all_goals norm_num
    linarith
  rw [h2, h5, h9]
  all_goals norm_num