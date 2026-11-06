import Mathlib

theorem algebra_15684 (c : ℝ) (h : ∃ x1 x2, x1 = (-11 + Real.sqrt 7) / 3 ∧ x2 = (-11 - Real.sqrt 7) / 3 ∧
    3 / 2 * x1 ^ 2 + 11 * x1 + c = 0 ∧ 3 / 2 * x2 ^ 2 + 11 * x2 + c = 0) :
    c = 19 := by
  rcases h with ⟨x1, x2, hx1, hx2, hx1_eq, hx2_eq⟩
  rw [hx1] at hx1_eq
  have h1 : 3 / 2 * ((-11 + Real.sqrt 7) / 3) ^ 2 + 11 * ((-11 + Real.sqrt 7) / 3) + c = 0 := by
    linarith
  have h2 : ((-11 + Real.sqrt 7) / 3 : ℝ) ^ 2 = (128 - 22 * Real.sqrt 7) / 9 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (7:ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (7:ℝ) by norm_num)]
  rw [h2] at h1
  nlinarith [Real.sqrt_pos.mpr (show 0 < (7:ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (7:ℝ) by norm_num)]