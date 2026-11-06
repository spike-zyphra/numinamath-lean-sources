import Mathlib

open BigOperators Real Set

theorem inequalities_171090 (x : ℝ) :
  x^2 * (x^4 + 36) - 6 * sqrt 3 * (x^4 + 4) < 0 ↔
  -12 ^ ((1 : ℝ) / 4) < x ∧ x < 12 ^ ((1 : ℝ) / 4) := by
  constructor
  · -- Assume x^2 * (x^4 + 36) - 6 * sqrt 3 * (x^4 + 4) < 0, prove -12^(1/4) < x ∧ x < 12^(1/4)
    intro h
    have h1 : x^2 * (x^4 + 36) - 6 * Real.sqrt 3 * (x^4 + 4) < 0 := by linarith
    have h2 : x^2 * (x^4 + 36) - 6 * Real.sqrt 3 * (x^4 + 4) = (x ^ 2 - 2 * Real.sqrt 3) ^ 3 := by
      ring_nf
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      have h4 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
        calc
          Real.sqrt 3 ^ 3 = (Real.sqrt 3 ^ 2) * Real.sqrt 3 := by ring
          _ = 3 * Real.sqrt 3 := by rw [h3]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3)]
    rw [h2] at h1
    have h3 : x ^ 2 - 2 * Real.sqrt 3 < 0 := by
      have h4 : (x ^ 2 - 2 * Real.sqrt 3) ^ 3 < 0 := by linarith
      have h5 : x ^ 2 - 2 * Real.sqrt 3 < 0 := by
        by_contra h
        push_neg at h
        have h6 : (x ^ 2 - 2 * Real.sqrt 3) ^ 3 ≥ 0 := by
          have h7 : x ^ 2 - 2 * Real.sqrt 3 ≥ 0 := by nlinarith
          have h8 : (x ^ 2 - 2 * Real.sqrt 3) ^ 3 ≥ 0 := by
            apply pow_nonneg
            linarith
          linarith
        linarith
      linarith
    have h4 : x ^ 2 < 2 * Real.sqrt 3 := by nlinarith
    have h5 : (2 * Real.sqrt 3) = Real.sqrt 12 := by
      have h10 : Real.sqrt 12 = Real.sqrt (4 * 3 : ℝ) := by norm_num
      have h11 : Real.sqrt (4 * 3 : ℝ) = (2 : ℝ) * Real.sqrt (3 : ℝ) := by
        calc
          Real.sqrt (4 * 3 : ℝ) = Real.sqrt (4 : ℝ) * Real.sqrt (3 : ℝ) := by
            rw [Real.sqrt_mul (by norm_num)]
          _ = (2 : ℝ) * Real.sqrt (3 : ℝ) := by
            have h3 : Real.sqrt (4 : ℝ) = 2 := by
              rw [Real.sqrt_eq_cases]
              all_goals norm_num
            rw [h3]
      rw [h10, h11]
    have h6 : x ^ 2 < Real.sqrt 12 := by
      nlinarith [h5]
    have h7 : x < (12 : ℝ) ^ ((1 : ℝ) / 4) := by
      have h9 : ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = Real.sqrt 12 := by
        have h10 : ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = (12 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        have h11 : (12 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 12 := by
          rw [Real.sqrt_eq_rpow]
        rw [h10, h11]
      have h11 : x ^ 2 < ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 := by
        nlinarith [h9]
      have h12 : 0 < (12 : ℝ) ^ ((1 : ℝ) / 4) := by
        positivity
      nlinarith [show (0 : ℝ) ≤ (12 : ℝ) ^ ((1 : ℝ) / 4) by positivity, sq_nonneg (x + (12 : ℝ) ^ ((1 : ℝ) / 4)), sq_nonneg (x - (12 : ℝ) ^ ((1 : ℝ) / 4)), sq_nonneg (x ^ 2), sq_nonneg ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ]
    have h8 : - (12 : ℝ) ^ ((1 : ℝ) / 4) < x := by
      have h9 : ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = Real.sqrt 12 := by
        have h10 : ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = (12 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        have h11 : (12 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 12 := by
          rw [Real.sqrt_eq_rpow]
        rw [h10, h11]
      have h11 : x ^ 2 < ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 := by
        nlinarith [h9]
      have h12 : 0 < (12 : ℝ) ^ ((1 : ℝ) / 4) := by
        positivity
      nlinarith [show (0 : ℝ) ≤ (12 : ℝ) ^ ((1 : ℝ) / 4) by positivity, sq_nonneg (x + (12 : ℝ) ^ ((1 : ℝ) / 4)), sq_nonneg (x - (12 : ℝ) ^ ((1 : ℝ) / 4)), sq_nonneg (x ^ 2), sq_nonneg ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ]
    constructor <;> nlinarith
  · -- Assume -12^(1/4) < x ∧ x < 12^(1/4), prove x^2 * (x^4 + 36) - 6 * sqrt 3 * (x^4 + 4) < 0
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 < ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 := by
      have h4 : 0 < (12 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
      nlinarith [show (0 : ℝ) ≤ (12 : ℝ) ^ ((1 : ℝ) / 4) by positivity, sq_nonneg (x + (12 : ℝ) ^ ((1 : ℝ) / 4)), sq_nonneg (x - (12 : ℝ) ^ ((1 : ℝ) / 4)), sq_nonneg (x ^ 2), sq_nonneg ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ]
    have h4 : ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = Real.sqrt 12 := by
      have h10 : ( (12 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = (12 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      have h11 : (12 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 12 := by
        rw [Real.sqrt_eq_rpow]
      rw [h10, h11]
    have h5 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
      have h10 : Real.sqrt 12 = Real.sqrt (4 * 3 : ℝ) := by norm_num
      have h11 : Real.sqrt (4 * 3 : ℝ) = (2 : ℝ) * Real.sqrt (3 : ℝ) := by
        calc
          Real.sqrt (4 * 3 : ℝ) = Real.sqrt (4 : ℝ) * Real.sqrt (3 : ℝ) := by
            rw [Real.sqrt_mul (by norm_num)]
          _ = (2 : ℝ) * Real.sqrt (3 : ℝ) := by
            have h3 : Real.sqrt (4 : ℝ) = 2 := by
              rw [Real.sqrt_eq_cases]
              all_goals norm_num
            rw [h3]
      rw [h10, h11]
    have h6 : x ^ 2 < 2 * Real.sqrt 3 := by
      nlinarith [h3, h4, h5]
    have h7 : (x ^ 2 - 2 * Real.sqrt 3) ^ 3 < 0 := by
      have h8 : x ^ 2 - 2 * Real.sqrt 3 < 0 := by nlinarith
      have h9 : (x ^ 2 - 2 * Real.sqrt 3) ^ 3 < 0 := by
        have h10 : (x ^ 2 - 2 * Real.sqrt 3) < 0 := by nlinarith
        have h11 : (x ^ 2 - 2 * Real.sqrt 3) ^ 3 = (x ^ 2 - 2 * Real.sqrt 3) * ((x ^ 2 - 2 * Real.sqrt 3) ^ 2) := by ring
        have h12 : (x ^ 2 - 2 * Real.sqrt 3) ^ 2 > 0 := by
          nlinarith [sq_pos_of_pos (show 0 < (2 : ℝ) by norm_num), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3 + 1)]
        nlinarith
      linarith
    have h8 : x^2 * (x^4 + 36) - 6 * Real.sqrt 3 * (x^4 + 4) = (x ^ 2 - 2 * Real.sqrt 3) ^ 3 := by
      ring_nf
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      have h4 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
        calc
          Real.sqrt 3 ^ 3 = (Real.sqrt 3 ^ 2) * Real.sqrt 3 := by ring
          _ = 3 * Real.sqrt 3 := by rw [h3]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3)]
    linarith [h8, h7]