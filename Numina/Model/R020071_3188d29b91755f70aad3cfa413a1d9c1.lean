import Mathlib

open Real Set
open scoped Real

theorem algebra_232112 (x : ℝ) : 3 * sin x + 4 * cos x = 2^(x + 3) + 2^(-x) ↔ False := by 
  constructor
  · -- Assume 3 * sin x + 4 * cos x = 2^(x + 3) + 2^(-x), prove False
    intro h_eq
    have h1 : -5 ≤ 3 * sin x + 4 * cos x := by
      have h2 : (3 * sin x + 4 * cos x) ≥ -5 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (3 * cos x - 4 * sin x), sq_nonneg (sin x * 4 + cos x * 3), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 3 / 5), sq_nonneg (cos x - 4 / 5), Real.sin_sq_add_cos_sq x]
      linarith
    have h2 : 3 * sin x + 4 * cos x ≤ 5 := by
      have h3 : (3 * sin x + 4 * cos x) ≤ 5 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (3 * cos x - 4 * sin x), sq_nonneg (sin x * 4 + cos x * 3), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 3 / 5), sq_nonneg (cos x - 4 / 5), Real.sin_sq_add_cos_sq x]
      linarith
    have h3 : (2 : ℝ) ^ (x + 3) + (2 : ℝ) ^ (-x) > 5 := by
      have h4 : (2 : ℝ) ^ (x + 3) = 8 * (2 : ℝ) ^ x := by 
        calc
          (2 : ℝ) ^ (x + 3) = (2 : ℝ) ^ x * (2 : ℝ) ^ (3 : ℝ) := by rw [Real.rpow_add]; all_goals linarith
          _ = (2 : ℝ) ^ x * (8 : ℝ) := by norm_num
          _ = 8 * (2 : ℝ) ^ x := by ring
      have h5 : (2 : ℝ) ^ (-x) = ((2 : ℝ) ^ x)⁻¹ := by 
        rw [Real.rpow_neg]
        all_goals linarith
      rw [h4, h5]
      have h6 : 0 < (2 : ℝ) ^ x := by positivity
      have h7 : 8 * ( (2 : ℝ) ^ x ) + ((2 : ℝ) ^ x)⁻¹ > 5 := by
        have h8 : ( (2 : ℝ) ^ x ) > 0 := by positivity
        have h9 : 8 * ( (2 : ℝ) ^ x ) + ((2 : ℝ) ^ x)⁻¹ - 5 > 0 := by
          have h10 : 8 * ( (2 : ℝ) ^ x ) + ((2 : ℝ) ^ x)⁻¹ - 5 = (8 * ( ( (2 : ℝ) ^ x ) ^ 2 ) + 1 - 5 * ( (2 : ℝ) ^ x )) / ( (2 : ℝ) ^ x ) := by 
            field_simp [show (2 : ℝ) ^ x ≠ 0 by positivity]
            <;> ring
          rw [h10]
          have h11 : 8 * ( ( (2 : ℝ) ^ x ) ^ 2 ) + 1 - 5 * ( (2 : ℝ) ^ x ) > 0 := by 
            nlinarith [sq_nonneg ( (2 : ℝ) ^ x - 1 / 2 ), sq_nonneg ( (2 : ℝ) ^ x - 2 / 1 ), 
              show 0 < (2 : ℝ) ^ x by positivity, sq_nonneg ( (2 : ℝ) ^ x ) ]
          have h12 : ( (2 : ℝ) ^ x ) > 0 := by positivity
          apply div_pos
          linarith
          linarith
        linarith
      linarith
    linarith [h_eq, h3, h2]
  · -- False → False
    intro h
    cases h