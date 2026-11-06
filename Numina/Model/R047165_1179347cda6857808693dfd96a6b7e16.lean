import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_197801 (x : ℝ) :
  (∀ y : ℝ, y^2 - (5^x - 1) * (y - 1) > 0) ↔ x ∈ Ioo 0 1 :=
  by
  constructor
  · -- First prove the forward direction: If the inequality holds for all y, then x ∈ (0, 1).
    intro h
    have h2 := h 0
    have h3 := h 2
    have h4 : (5:ℝ) ^ x > (1:ℝ) := by
      nlinarith [h2, Real.rpow_pos_of_pos (show (0 : ℝ) < 5 by norm_num) x]
    have h5 : (5:ℝ) ^ x < (5:ℝ) := by
      nlinarith [h3, h4]
    constructor
    · -- Prove x > 0
      by_contra h0
      push_neg at h0
      have h50 : (5 : ℝ) ^ x ≤ (1 : ℝ) := by
        have h00 : (5:ℝ) ^ (x) ≤ (5:ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
        norm_num at h00 ⊢
        linarith
      linarith
    · -- Prove x < 1
      by_contra h1
      push_neg at h1
      have h51 : (5 : ℝ) ^ x ≥ (5 : ℝ) := by
        have h01 : (5 : ℝ) ^ (x) ≥ (5 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
        norm_num at h01 ⊢
        linarith
      linarith
  · -- Now the reverse direction: If x ∈ (0, 1), then the inequality holds for all y.
    rintro ⟨hx1, hx2⟩
    intro y
    have h3 : (5 : ℝ) ^ x > (1 : ℝ) := by
      have : (5 : ℝ) ^ x > (5 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      norm_num at this ⊢
      linarith
    have h4 : (5 : ℝ) ^ x < (5 : ℝ) := by
      have : (5 : ℝ) ^ x < (5 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      norm_num at this ⊢
      linarith
    have h5 : ( (5 : ℝ) ^ x - 1 ) * ( (5 : ℝ) ^ x - 5 ) < (0 : ℝ) := by
      have h6 : 0 < (5 : ℝ) ^ x - 1 := by linarith
      have h7 : (5 : ℝ) ^ x - 5 < 0 := by linarith
      nlinarith
    nlinarith [ sq_nonneg (y - ( (5^x - 1) / 2 ) ), sq_nonneg (y - 2), sq_nonneg (y - 0),
              Real.rpow_pos_of_pos (show (0 : ℝ) < 5 by norm_num) x, Real.rpow_pos_of_pos (show (0 : ℝ) < 5 by norm_num) x, h5 ]