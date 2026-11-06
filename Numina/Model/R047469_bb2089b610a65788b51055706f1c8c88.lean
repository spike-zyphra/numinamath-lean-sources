import Mathlib

theorem algebra_227347 : ∃ q : ℚ, (Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3) = q := by
  use (1 : ℚ)
  have h1 : Real.sqrt 5 ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 5 + 2 : ℝ) ≥ 0 := by
    have h1 : Real.sqrt 5 ≥ 0 := by
      apply Real.sqrt_nonneg
    linarith
  have h4 : (Real.sqrt 5 - 2 : ℝ) ≥ 0 := by
    have h5 : Real.sqrt 5 ≥ 2 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    linarith
  have h5 : ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = 4 - 3 * ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) := by
    have h7 : ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (Real.sqrt 5 + 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h8 : ( (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (Real.sqrt 5 - 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h9 : ( (Real.sqrt 5 + 2 : ℝ) * (Real.sqrt 5 - 2 : ℝ) ) = (1 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h10 : ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) ) * ( (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) = (1 : ℝ) := by
      have h11 : ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) ) * ( (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) = ( (Real.sqrt 5 + 2 : ℝ) * (Real.sqrt 5 - 2 : ℝ) ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.mul_rpow]
        all_goals
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h11, h9]
      all_goals
        norm_num
    calc
      ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3
        = ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 - ( (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 - 3 * (( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) ) * ( (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ) * ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) := by
          ring
      _ = ( (Real.sqrt 5 + 2 : ℝ) ) - ( (Real.sqrt 5 - 2 : ℝ) ) - 3 * ( (1 : ℝ) ) * ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) := by
        rw [h7, h8, h10]
      _ = 4 - 3 * ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) := by
        ring_nf
  have h6 : (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) = (1 : ℝ) := by
    have h7 : ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 + 3 * ((Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) - 4 = (0 : ℝ) := by
      nlinarith [h5]
    have h8 : ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) - (1 : ℝ) ) * ( ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 + ( ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ) + (4 : ℝ) ) = (0 : ℝ) := by
      nlinarith [h7]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- First case
      have h8 : (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) = (1 : ℝ) := by
        linarith
      exact h8
    · -- Second case
      -- Show it's impossible. $ a * real ^ 2 + ... + 4 d * 4 = 0 nlinarith [ ... ] $
      have h9 : ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 + ( ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ) ) + (4 : ℝ) = (0 : ℝ) := by
        linarith
      nlinarith [ sq_nonneg ( (Real.sqrt 5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2 : ℝ) ^ ((1 : ℝ) / 3) + 1 / 2 ) ]
  exact_mod_cast h6