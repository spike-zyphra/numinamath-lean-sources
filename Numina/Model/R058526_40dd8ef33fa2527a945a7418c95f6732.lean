import Mathlib

open Real

theorem algebra_188341 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h₁ : logb 4 x + logb 4 y = 1 + logb 4 9) (h₂ : x + y - 20 = 0) :
    (x = 2 ∧ y = 18) ∨ (x = 18 ∧ y = 2) := by 
  have h3 : logb 4 x + logb 4 y = logb 4 (x * y) := by
    rw [logb_mul (by linarith) (by linarith)]
  have h4 : (1 : ℝ) + logb 4 9 = logb 4 36 := by 
    have h5 : (1 : ℝ) = logb 4 (4 : ℝ) := by 
      rw [logb_self_eq_one]
      all_goals linarith
    rw [h5]
    have h6 : logb 4 (4 : ℝ) + logb 4 9 = logb 4 (4 * 9 : ℝ) := by 
      rw [logb_mul (by norm_num) (by norm_num)]
    rw [h6]
    all_goals norm_num
  rw [h3] at h₁
  rw [h4] at h₁ 
  have h7 : x * y = 36 := by 
    have h8 : logb 4 (x * y) = logb 4 36 := by 
      linarith
    have h9 : x * y > 0 := mul_pos hx hy
    have h10 : (x * y) = 36 := by 
      apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h9) (Set.mem_Ioi.mpr (by norm_num)) h8
    linarith
  have h8 : x + y = 20 := by 
    linarith
  have h9 : y = 20 - x := by 
    linarith
  rw [h9] at h7 
  have h10 : x ^ 2 - 20 * x + 36 = 0 := by 
    nlinarith 
  have h11 : (x - 2) * (x - 18) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.1 h11) with h12 h13 
  · -- case x = 2 
    have hx2 : x = 2 := by linarith 
    have hy18 : y = 18 := by 
      nlinarith 
    left 
    exact ⟨hx2, hy18⟩ 
  · -- case x = 18 
    have hx18 : x = 18 := by linarith 
    have hy2 : y = 2 := by 
      nlinarith 
    right 
    exact ⟨hx18, hy2⟩