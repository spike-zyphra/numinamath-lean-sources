import Mathlib

theorem algebra_164354 (x : ℝ) (hx : x = 5 ∨ x = (2 - 3 * Real.sqrt 11) / 2) :
    Real.sqrt (x + 4) - Real.sqrt (6 - x) + 4 = 2 * Real.sqrt (24 + 2 * x - x ^ 2) := by
  rcases hx with (r | r)
  · -- first case
    rw [r]
    have h1 : Real.sqrt ((5 : ℝ) + 4) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((6 - (5 : ℝ)) ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt ((24 + 2 * (5 : ℝ) - (5 : ℝ) ^ 2)) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num
  · -- second case
    rw [r]
    have h1 : Real.sqrt (( (2 - 3 * Real.sqrt 11) / 2 : ℝ ) + 4 ) = Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) := by
      ring_nf
    have h2 : Real.sqrt ((6 - ( (2 - 3 * Real.sqrt 11 ) / 2 : ℝ ) )) = Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) := by
      ring_nf
    have h3 : Real.sqrt (24 + 2 * (( (2 - 3 * Real.sqrt 11 ) / 2 : ℝ )) - (( (2 - 3 * Real.sqrt 11 ) / 2 : ℝ )) ^ 2) = (1 / 2 : ℝ) := by
      have h31 : (24 + 2 * (( (2 - 3 * Real.sqrt 11 ) / 2 : ℝ )) - (( (2 - 3 * Real.sqrt 11 ) / 2 : ℝ )) ^ 2 ) = (1 / 4 : ℝ) := by
        nlinarith [ Real.sqrt_pos.mpr (show 0 < (11 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num) ]
      rw [h31]
      have h32 : Real.sqrt ((1 / 4 : ℝ) ) = (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h32]
    have eq1 : Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) ^ 2 = ( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ) := by
      apply Real.sq_sqrt
      nlinarith [ Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num) ]
    have eq2 : Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ^ 2 = ( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ) := by
      apply Real.sq_sqrt
      nlinarith [ Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num) ]
    have h4 : Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) - Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) = -3 := by
      have h41 : (Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) - Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ) ^ 2 = 9 := by
        have h41_1 : Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) ^ 2 = ( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ) := eq1
        have h41_2 : Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ^ 2 = ( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ) := eq2
        have h41_3 : (Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) * Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ) = (1 / 2 : ℝ) := by
          have h41_31 : (Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) * Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ) ^ 2 = (1 / 4 : ℝ) := by
            calc
              (Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) * Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ) ^ 2
                  = (Real.sqrt ( ( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ) ) ^ 2 ) * (Real.sqrt ( ( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ) ) ^ 2 ) := by ring
              _ = ( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ) * ( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ) := by
                rw [h41_1, h41_2]
              _ = (1 / 4 : ℝ) := by
                nlinarith [ Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num) ]
          have h41_32 : 0 ≤ (Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) * Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) : ℝ) := by positivity
          have h41_33 : (Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) * Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ) = Real.sqrt ( ( (Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) * Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) ) ^ 2 : ℝ) ) := by
            rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) * Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) by positivity ) ]
          rw [h41_33]
          rw [h41_31]
          have h41_35 : Real.sqrt ( (1 / 4 : ℝ) ) = (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h41_35]
        nlinarith
      have h42 : Real.sqrt (( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ)) ≤ Real.sqrt (( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ)) := by
        apply Real.sqrt_le_sqrt
        nlinarith [ Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num) ]
      nlinarith [ Real.sqrt_nonneg ( ( (10 - 3 * Real.sqrt 11 ) / 2 : ℝ) ), Real.sqrt_nonneg ( ( (10 + 3 * Real.sqrt 11 ) / 2 : ℝ) ), h42 ]
    rw [h1, h2, h3]
    nlinarith [h4]