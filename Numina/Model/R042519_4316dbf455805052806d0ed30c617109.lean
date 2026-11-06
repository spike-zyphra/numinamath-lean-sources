import Mathlib

open Real

theorem algebra_13921 (a b c : ℝ)(ha : 0 < a)(hb : 0 < b)(hc : 0 < c):
(24 * a ^ (4:ℝ) * b ^ (6:ℝ) * c ^ (11:ℝ)) ^ ((1:ℝ)/3) =
2 * a ^ (1:ℝ) * b ^ (2:ℝ) * c ^ (3:ℝ) * (3 * a * c ^ (2:ℝ)) ^ ((1:ℝ)/3) ∧ 1 + 2 + 3 = 6 := by

  constructor
  · -- Prove the expression simplifies correctly
    have h1 : (24 * a ^ (4:ℝ) * b ^ (6:ℝ) * c ^ (11:ℝ)) ^ ((1:ℝ)/3) =
      2 * a ^ (1:ℝ) * b ^ (2:ℝ) * c ^ (3:ℝ) * (3 * a * c ^ (2:ℝ)) ^ ((1:ℝ)/3) := by
      have h2 : (24 * a ^ (4:ℝ) * b ^ (6:ℝ) * c ^ (11:ℝ)) ^ ((1:ℝ)/3) =
        ((24:ℝ) * (a^4) * (b^6) * (c^11)) ^ ((1:ℝ)/3) := by
        norm_cast
      rw [h2]
      have h3 : ((24:ℝ) * (a^4) * (b^6) * (c^11)) ^ ((1:ℝ)/3) =
          (24:ℝ) ^ ((1:ℝ)/3) * ((a^4) : ℝ) ^ ((1:ℝ)/3) * ((b^6) : ℝ) ^ ((1:ℝ)/3) * ((c^11) : ℝ) ^ ((1:ℝ)/3) := by
        rw [← Real.mul_rpow]
        rw [← Real.mul_rpow]
        rw [← Real.mul_rpow]
        all_goals
          positivity
      rw [h3]
      have h4 : (24:ℝ) ^ ((1:ℝ)/3) = 2 * (3:ℝ) ^ ((1:ℝ)/3) := by
        have h5 : (24:ℝ) ^ ((1:ℝ)/3) = (2^3 * 3) ^ ((1:ℝ)/3) := by norm_num
        have h6 : (2^3 * (3:ℝ)) ^ ((1:ℝ)/3) = (2^3:ℝ) ^ ((1:ℝ)/3) * (3:ℝ) ^ ((1:ℝ)/3) := by
          rw [← Real.mul_rpow]
          all_goals
            norm_num
        have h7 : (2^3:ℝ) ^ ((1:ℝ)/3) = (2:ℝ) := by
          have h8 : (2^3:ℝ) ^ ((1:ℝ)/3) = (2:ℝ) := by
            rw [show (2 ^ 3: ℝ) = (8: ℝ) by norm_num]
            have h9 : (8: ℝ) ^ ((1: ℝ) / 3) = 2 := by
              rw [show (8: ℝ) = 2 ^ 3 by norm_num]
              rw [← Real.rpow_natCast]
              rw [← Real.rpow_mul]
              norm_num
              all_goals
                linarith
            linarith
          linarith
        rw [h5, h6, h7]
      have h5 : ((a^4) : ℝ) ^ ((1:ℝ)/3) = a ^ (1:ℝ) * (a: ℝ) ^ ((1:ℝ)/3) := by
        have h11 : ((a^4) : ℝ) ^ ((1:ℝ)/3) = a ^ (4/3: ℝ) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul]
          norm_num
          all_goals
            positivity
        have h12 : a ^ (4/3: ℝ) = a ^ (1: ℝ) * a ^ (1/3: ℝ) := by
          rw [show (4/3: ℝ) = (1: ℝ) + (1/3: ℝ) by norm_num]
          rw [Real.rpow_add]
          norm_num
          all_goals
            positivity
        rw [h11, h12]
      have h6 : ((b^6) : ℝ) ^ ((1:ℝ)/3) = b ^ (2: ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals
          positivity
      have h7 : ((c^11) : ℝ) ^ ((1:ℝ)/3) = c ^ (3: ℝ) * (c: ℝ) ^ (2/3: ℝ) := by
        have h13 : ((c^11) : ℝ) ^ ((1:ℝ)/3) = c ^ (11/3: ℝ) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul]
          norm_num
          all_goals
            positivity
        have h14 : c ^ (11/3: ℝ) = c ^ (3: ℝ) * c ^ (2/3: ℝ) := by
          rw [show (11/3: ℝ) = (3: ℝ) + (2/3: ℝ) by norm_num]
          rw [Real.rpow_add]
          norm_num
          all_goals
            positivity
        rw [h13, h14]
      rw [h4, h5, h6, h7]
      have h8 : (3 * a * c ^ (2:ℝ)) ^ ((1:ℝ)/3) = (3: ℝ) ^ ((1: ℝ)/3) * (a: ℝ) ^ ((1: ℝ)/3) * (c ^ (2: ℝ)) ^ ((1: ℝ)/3) := by
        rw [← Real.mul_rpow]
        rw [← Real.mul_rpow]
        all_goals
          positivity
      have h9 : (c ^ (2:ℝ)) ^ ((1: ℝ)/3) = (c: ℝ) ^ (2/3: ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals
          positivity
      rw [h8, h9]
      ring_nf
    exact h1
  · -- Show the exponents sum to 6
    norm_num