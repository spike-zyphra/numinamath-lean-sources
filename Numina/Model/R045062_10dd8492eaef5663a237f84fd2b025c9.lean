import Mathlib

theorem algebra_11251 (A B : ℝ × ℝ) (hA : A.1^2 - A.2^2 = 1) (hB : B.1^2 - B.2^2 = 1)
    (hAB : A ≠ B) (k : ℝ) (hk : k = (A.2 - B.2) / (A.1 - B.1)) :
    k * (-2) + 1 > -2 - Real.sqrt 2 ∨ k * (-2) + 1 < 2 := by
  by_contra h
  push_neg at h
  have h0 : k * (-2) + 1 ≤ -2 - Real.sqrt 2 ∧ k * (-2) + 1 ≥ 2 := by 
    exact h
  linarith [h0.left, h0.right, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]