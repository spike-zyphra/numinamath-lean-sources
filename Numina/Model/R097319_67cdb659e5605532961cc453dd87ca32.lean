import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_180609 :
  IsLeast {d | ∃ A B : ℝ × ℝ,
    A.1^2 - A.2 + 1 = 0 ∧ B.2^2 - B.1 + 1 = 0 ∧
    d = Real.sqrt ((A.1 - B.1)^2 + (A.2 - B.2)^2)} (3 * sqrt 2 / 4) := by
  constructor
  · -- Show that 3 * sqrt 2 / 4 is in the set
    use (1 / 2, 5 / 4)
    use (5 / 4, 1 / 2)
    constructor
    · -- Verify point A is on curve C₁
      norm_num
    constructor
    · -- Verify point B is on curve C₂
      norm_num
    · -- Compute the distance and verify it's 3 * sqrt 2 / 4
      have h1 : Real.sqrt ((1 / 2 - 5 / 4) ^ 2 + (5 / 4 - 1 / 2) ^ 2) = 3 * Real.sqrt 2 / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
        <;> ring_nf
        <;> norm_num
      linarith [h1]
  · -- Now prove that 3 * sqrt 2 / 4 is indeed the least element
    rintro d ⟨A, B, hA, hB, h1d⟩
    have ha : A.2 = A.1 ^ 2 + 1 := by linarith
    have hb : B.1 = B.2 ^ 2 + 1 := by linarith
    have h2 : (A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2 ≥ 9 / 8 := by
      rw [show A.2 = A.1^2 + 1 by linarith [ha]]
      rw [show B.1 = B.2^2 + 1 by linarith [hb]]
      nlinarith [sq_nonneg (A.1 - 1 / 2), sq_nonneg (B.2 - 1 / 2), sq_nonneg (A.1 - B.2), sq_nonneg (A.1 + B.2 - 1), 
          sq_nonneg (A.1 - B.2 - 1 / 2), sq_nonneg (B.2 - 1 / 2), sq_nonneg (A.1 - 1 / 2),
          sq_nonneg ((A.1 - 1 / 2) - (B.2 - 1 / 2)), sq_nonneg ((A.1 - 1 / 2) + (B.2 - 1 / 2)), 
          mul_nonneg (sq_nonneg (A.1 - 1 / 2)) (sq_nonneg (B.2 - 1 / 2)), 
          Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : Real.sqrt ((A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2) ≥ Real.sqrt (9 / 8) := by
      have h5 : (A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2 ≥ 9 / 8 := by
        nlinarith [sq_nonneg (A.1 - 1 / 2), sq_nonneg (B.2 - 1 / 2), sq_nonneg (A.1 - B.2), sq_nonneg (A.1 + B.2 - 1), 
          sq_nonneg (A.1 - B.2 - 1 / 2), sq_nonneg (B.2 - 1 / 2), sq_nonneg (A.1 - 1 / 2),
          sq_nonneg ((A.1 - 1 / 2) - (B.2 - 1 / 2)), sq_nonneg ((A.1 - 1 / 2) + (B.2 - 1 / 2)), 
          mul_nonneg (sq_nonneg (A.1 - 1 / 2)) (sq_nonneg (B.2 - 1 / 2)), 
          Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        ]
      apply Real.sqrt_le_sqrt
      nlinarith
    have h4 : Real.sqrt (9 / 8) = 3 * Real.sqrt 2 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
    linarith [h1d, h3, h4]