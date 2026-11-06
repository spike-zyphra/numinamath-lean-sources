import Mathlib

theorem algebra_207468 (a b : ℝ) (hf : ∀ x ∈ Set.Icc 0 1, |a * x + b| ≤ 1) :
    a * b ≤ 1 / 4 := by
  have h1 := hf 0 (Set.left_mem_Icc.mpr (by linarith))
  have h2 := hf 1 (Set.right_mem_Icc.mpr (by linarith))
  have h3 := hf (1 / 2) (by norm_num)
  have hb1 : -1 ≤ b := by 
    linarith [abs_le.mp h1]
  have hb2 : b ≤ 1 := by 
    linarith [abs_le.mp h1]
  have h21 : -1 ≤ a + b := by 
    linarith [abs_le.mp h2]
  have h22 : a + b ≤ 1 := by 
    linarith [abs_le.mp h2]
  have h31 : -1 ≤ a * (1 / 2) + b := by 
    linarith [abs_le.mp h3]
  have h32 : a * (1 / 2) + b ≤ 1 := by 
    linarith [abs_le.mp h3]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), abs_le.mp h1, abs_le.mp h2, abs_le.mp h3]