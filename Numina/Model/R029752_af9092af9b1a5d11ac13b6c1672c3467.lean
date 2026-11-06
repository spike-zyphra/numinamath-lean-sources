import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_321630 :
  IsLeast {d | ∃ P Q : ℝ × ℝ,
    P.2 = -P.1^2 - 1 ∧ Q.1 = 1 + Q.2^2 ∧
    d = Real.sqrt ((P.1 - Q.1)^2 + (P.2 - Q.2)^2)} (3 * sqrt 2 / 4) := by
  constructor
  · -- Show 3 * sqrt(2) / 4 is in the set.
    use (1 / 2, -5 / 4)
    use (5 / 4, -1 / 2)
    constructor
    · -- Check P's constraint
      norm_num
    constructor
    · -- Check Q's constraint
      norm_num
    · -- Show the distance is 3 * sqrt(2) / 4
      have h1 : Real.sqrt (( (1 / 2 : ℝ) - (5 / 4 : ℝ) ) ^ 2 + ( (-5 / 4 : ℝ) - (-1 / 2 : ℝ) ) ^ 2) = 3 * Real.sqrt 2 / 4 := by
        have h2 : ((1 / 2 : ℝ) - (5 / 4 : ℝ)) ^ 2 + ((-5 / 4 : ℝ) - (-1 / 2 : ℝ)) ^ 2 = (9 / 8 : ℝ) := by
          norm_num
        rw [h2]
        have h3 : (3 * Real.sqrt 2 / 4) ^ 2 = (9 / 8 : ℝ) := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h4 : 0 ≤ (3 * Real.sqrt 2 / 4 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        rw [Real.sqrt_eq_iff_sq_eq] <;> (nlinarith [h3, h4, Real.sqrt_nonneg (2 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])
      linarith [h1]
  · -- Show 3 * sqrt(2) / 4 is the least
    intro d
    rintro ⟨P, Q, hP, hQ, hd⟩
    have h1 : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 ≥ (9 / 8 : ℝ) := by
      have h1 : Q.1 = 1 + Q.2 ^ 2 := by
        linarith [hQ]
      have h2 : P.2 = -P.1^2 - 1 := by
        linarith [hP]
      rw [h1, h2]
      nlinarith [sq_nonneg (P.1 - 1 / 2 : ℝ), sq_nonneg (Q.2 + 1 / 2 : ℝ),
        sq_nonneg (P.1 - 1 / 2 + (Q.2 + 1 / 2) : ℝ), sq_nonneg (P.1 - 1 / 2 - (Q.2 + 1 / 2) : ℝ),
        sq_nonneg (P.1 ^ 2 - 1 / 4 : ℝ), sq_nonneg (Q.2 ^ 2 - 1 / 4 : ℝ),
        sq_nonneg (P.1 ^ 2 + Q.2 ^ 2 - 1 / 2 : ℝ), sq_nonneg ((P.1) ^ 2 + (Q.2) ^ 2 - 1 / 2 : ℝ),
        sq_nonneg ((P.1) + (Q.2) : ℝ), sq_nonneg ((P.1) - (Q.2) : ℝ),
        sq_nonneg ((P.1) ^ 2 - (Q.2) ^ 2 : ℝ), sq_nonneg ((P.1) * (Q.2) : ℝ),
        sq_nonneg (P.1 ^ 2 - 1 / 4 : ℝ), sq_nonneg (Q.2 ^ 2 - 1 / 4 : ℝ)
      ]
    have h2 : Real.sqrt ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) ≥ Real.sqrt (9 / 8 : ℝ) := Real.sqrt_le_sqrt (show (9 / 8 : ℝ) ≤ (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 by linarith [h1])
    have h3 : Real.sqrt ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) ≥ 3 * Real.sqrt 2 / 4 := by
      have h4 : Real.sqrt (9 / 8 : ℝ) = 3 * Real.sqrt 2 / 4 := by
        have h5 : (3 * Real.sqrt 2 / 4) ^ 2 = (9 / 8 : ℝ) := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h8 : Real.sqrt (9 / 8 : ℝ) = Real.sqrt ((3 * Real.sqrt 2 / 4) ^ 2) := by
          rw [h5]
        have h9 : Real.sqrt ((3 * Real.sqrt 2 / 4) ^ 2) = (3 * Real.sqrt 2 / 4 : ℝ) := by
          rw [Real.sqrt_sq (show 0 ≤ (3 * Real.sqrt 2 / 4 : ℝ) by
            nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
          )]
        rw [h8, h9]
      linarith [h4, h2]
    linarith [h3, hd]