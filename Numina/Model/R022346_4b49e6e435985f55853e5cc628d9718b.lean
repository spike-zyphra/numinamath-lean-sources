import Mathlib

open Real

theorem inequalities_84553 (x y : ℝ) (hx : -1 < x) (hy : -1 < y) (hxy : x + y = 1) :
    2 / 3 ≤ x / (y + 1) + y / (x + 1) ∧
    (2 / 3 = x / (y + 1) + y / (x + 1) ↔ x = y) := by
  have h1 : 0 < y + 1 := by linarith
  have h2 : 0 < x + 1 := by linarith
  constructor
  · -- First part: prove the inequality.
    have h3 : x / (y + 1) + y / (x + 1) ≥ (2 : ℝ) / 3 := by
      have h4 : x / (y + 1) + y / (x + 1) - (2 / 3) ≥ 0 := by
        have pos1 : 0 < (y + 1) * (x + 1) := mul_pos h1 h2
        have h5 : x / (y + 1) + y / (x + 1) - (2 / 3) =
            (3 * x * (x + 1) + 3 * y * (y + 1) - 2 * (y + 1) * (x + 1)) / (3 * ( (y + 1) * (x + 1)))
            := by
            field_simp
            ring
        rw [h5] at *
        have h6 : 3 * x * (x + 1) + 3 * y * (y + 1) - 2 * (y + 1) * (x + 1) ≥ 0 := by
          have h7 : y = 1 - x := by linarith
          rw [h7]
          nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2), sq_nonneg (x - (1 - x)), mul_pos (show 0 < x + 1 by linarith) (show 0 < (1 - x) + 1 by nlinarith)]
        have h8 : (3 * ( (y + 1) * (x + 1) )) > 0 := by positivity
        apply div_nonneg
        linarith
        all_goals positivity
      linarith
    linarith [h3]
  · -- Second part: prove the equality holds iff x = y.
    constructor
    · -- Forward: if 2/3 = LHS, then x = y.
      intro heq
      have h4 : x / (y + 1) + y / (x + 1) = (2 : ℝ) / 3 := by linarith
      have h5 : (3 * x * (x + 1) + 3 * y * (y + 1) - 2 * (y + 1) * (x + 1)) = 0 := by 
        field_simp [show 0 < y + 1 by linarith, show 0 < x + 1 by linarith] at h4 ⊢
        ring_nf at h4 ⊢
        nlinarith
      have h7 : y = 1 - x := by linarith
      rw [h7] at h5
      have h8 : (x - 1 / 2) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2), sq_nonneg (x - (1 - x)), mul_pos (show 0 < x + 1 by linarith) (show 0 < (1 - x) + 1 by nlinarith)]
      have h9 : x - 1 / 2 = 0 := by
        rw [sq_eq_zero_iff] at h8
        exact h8
      have hx1 : x = 1 / 2 := by linarith
      have hy1 : y = 1 / 2 := by
        linarith
      linarith
    · -- Backward: if x = y, then 2/3 = LHS.
      intro heq
      have h_eq : x = y := heq
      have h7 : x = 1 / 2 := by
        have h8 : y = x := by linarith [h_eq]
        nlinarith
      have h8 : y = 1 / 2 := by
        linarith
      rw [show x = (1 / 2 : ℝ) by linarith, show y = (1 / 2 : ℝ) by linarith]
      norm_num