import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_104628 {x: ℝ} :  (0 < (3:ℝ)^x - 1 ∧ 0 < (9:ℝ)^x - (3:ℝ)^(x+1) + 2 ∧ 0 < 3 - (3:ℝ)^x) ↔ x ∈ Ioo (logb 3 2) (1) := by
  constructor
  · -- Assume all three conditions are satisfied, prove x ∈ Ioo (logb 3 2) (1)
    rintro ⟨h1, h2, h3⟩
    have h4 : (3 : ℝ) ^ x > (1 : ℝ) := by linarith
    have h5 : x > (0 : ℝ) := by
      by_contra h
      push_neg at h
      have h6 : x ≤ (0 : ℝ) := by linarith
      have h7 : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals linarith
      have h8 : (3 : ℝ) ^ (0 : ℝ) = 1 := by
        simp
      rw [h8] at h7
      linarith
    have h6 : (9 : ℝ) ^ x - (3 : ℝ) ^ (x + 1) + 2 > (0 : ℝ) := h2
    have h7 : (9 : ℝ) ^ x = ((3 : ℝ) ^ x) ^ 2 := by
      calc
        (9 : ℝ) ^ x = (3 ^ (2 : ℝ) ) ^ x := by norm_num
        _ = 3 ^ (2 * x : ℝ) := by rw [← Real.rpow_mul]; ring_nf; all_goals linarith
        _ = ((3 : ℝ) ^ x) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
    have h8 : (3 : ℝ) ^ (x + 1) = 3 * ((3 : ℝ) ^ x) := by
      rw [Real.rpow_add]
      ring_nf
      all_goals linarith
    rw [h7, h8] at h6
    have h9 : ((3 : ℝ) ^ x - 1) * ((3 : ℝ) ^ x - 2) > 0 := by
      nlinarith
    have h10 : (3 : ℝ) ^ x > (2 : ℝ) := by
      by_contra h
      push_neg at h
      have h11 : (3 : ℝ) ^ x ≤ (2 : ℝ) := by linarith
      nlinarith
    have h11 : x > logb 3 2 := by
      by_contra h
      push_neg at h
      have h12 : x ≤ logb 3 2 := by linarith
      have h13 : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ (logb 3 2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals linarith
      have h14 : (3 : ℝ) ^ (logb 3 2 : ℝ) = (2 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals norm_num
      rw [h14] at h13
      nlinarith
    have h15 : x < (1 : ℝ) := by
      by_contra h
      push_neg at h
      have h16 : x ≥ (1 : ℝ) := by linarith
      have h17 : (3 : ℝ) ^ x ≥ (3 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals linarith
      have h18 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by
        simp
      rw [h18] at h17
      have h19 : (3 : ℝ) ^ x ≥ (3 : ℝ) := by
        linarith
      nlinarith
    constructor <;> linarith
  · -- Assume x ∈ Ioo (logb 3 2) (1), prove all three conditions are satisfied
    rintro ⟨h1, h2⟩
    constructor
    · -- 0 < (3:ℝ)^x - 1
      have h3 : (3 : ℝ) ^ x > (1 : ℝ) := by
        have h4 : x > (0 : ℝ) := by
          have h5 : logb 3 2 > (0 : ℝ) := by
            apply logb_pos
            all_goals norm_num
          nlinarith
        have h5 : (3 : ℝ) ^ x > (3 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h6 : (3 : ℝ) ^ (0 : ℝ) = 1 := by
          simp
        rw [h6] at h5
        linarith
      linarith
    constructor
    · -- 0 < (9:ℝ)^x - (3:ℝ)^(x+1) + 2
      have h4 : (9 : ℝ) ^ x - (3 : ℝ) ^ (x + 1) + 2 > (0 : ℝ) := by
        have h7 : (9 : ℝ) ^ x = ((3 : ℝ) ^ x) ^ 2 := by
          calc
            (9 : ℝ) ^ x = (3 ^ (2 : ℝ) ) ^ x := by norm_num
            _ = 3 ^ (2 * x : ℝ) := by rw [← Real.rpow_mul]; ring_nf; all_goals linarith
            _ = ((3 : ℝ) ^ x) ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              ring_nf
              all_goals linarith
        have h8 : (3 : ℝ) ^ (x + 1) = 3 * ((3 : ℝ) ^ x) := by
          rw [Real.rpow_add]
          ring_nf
          all_goals linarith
        rw [h7, h8]
        have h4' : (3 : ℝ) ^ x > (2 : ℝ) := by
          have h5 : x > logb 3 2 := by
            linarith [h1]
          have h6 : (3 : ℝ) ^ x > (3 : ℝ) ^ (logb 3 2 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals linarith
          have h7 : (3 : ℝ) ^ (logb 3 2 : ℝ) = (2 : ℝ) := by
            rw [Real.rpow_logb]
            all_goals norm_num
          rw [h7] at h6
          nlinarith
        nlinarith [sq_nonneg ((3 : ℝ) ^ x - 2), sq_nonneg ((3 : ℝ) ^ x - 1)]
      linarith
    · -- 0 < 3 - (3:ℝ)^x
      have h8 : (3 : ℝ) ^ x < (3 : ℝ) := by
        have h9 : x < (1 : ℝ) := by
          linarith
        have h10 : (3 : ℝ) ^ x < (3 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h11 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by
          simp
        rw [h11] at h10
        linarith
      linarith