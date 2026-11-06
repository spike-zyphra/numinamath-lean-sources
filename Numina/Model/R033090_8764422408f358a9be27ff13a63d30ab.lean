import Mathlib

open Real

theorem inequalities_260484 (x y : ℝ) (hx : -1 < x) (hy : -1 < y)
    (hxy : x + y = 1) :
    x / (y + 1) + y / (x + 1) ≥ 2 / 3 ∧
    (x / (y + 1) + y / (x + 1) = 2 / 3 ↔ x = y) := by
  have h1 : 0 < y + 1 := by linarith
  have h2 : 0 < x + 1 := by linarith
  constructor
  · -- Prove the inequality
    have h3 : x / (y + 1) + y / (x + 1) - 2 / 3 ≥ 0 := by
      have h4 : x / (y + 1) + y / (x + 1) - 2 / 3 =
          ( 3 * x * (x + 1) + 3 * y * (y + 1) - 2 * ( (y + 1) * (x + 1) ) ) / ( 3 * (y + 1) * (x + 1) ) := by
        field_simp
        <;> ring
      rw [h4]
      apply div_nonneg
      · -- Show the numerator is non-negative
        have h5 : 3 * x * (x + 1) + 3 * y * (y + 1) - 2 * ( (y + 1) * (x + 1) ) ≥ 0 := by
          have h6 : y = 1 - x := by linarith
          rw [show y = 1 - x by linarith]
          nlinarith [ sq_nonneg (x - 1 / 2), sq_nonneg (x - y), sq_nonneg ((1 - x) - 1 / 2) ]
        linarith
      · -- Show the denominator is positive
        positivity
    linarith
  · -- Prove the equality condition
    constructor
    · -- Forward: equality holds implies x = y
      intro heq
      have h3 : x / (y + 1) + y / (x + 1) - 2 / 3 = 0 := by
        linarith
      have h4 : ( 3 * x * (x + 1) + 3 * y * (y + 1) - 2 * ( (y + 1) * (x + 1) ) ) = 0 := by
        have h11 : x / (y + 1) + y / (x + 1) - 2 / 3 =
            ( 3 * x * (x + 1) + 3 * y * (y + 1) - 2 * ( (y + 1) * (x + 1) ) ) / ( 3 * (y + 1) * (x + 1) ) := by
          field_simp
          <;> ring
        rw [h11] at h3
        have pos1 : 3 * (y + 1) * (x + 1) > 0 := by positivity
        field_simp at h3 ⊢
        <;> nlinarith
      have h5 : (2 * (x - 1 / 2) ) ^ 2 = 0 := by
        have h6 : y = 1 - x := by linarith
        rw [show y = 1 - x by linarith] at h4
        nlinarith [ sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2) ]
      have h8 : 2 * (x - 1 / 2) = 0 := by
        apply pow_eq_zero
        exact h5
      have h9 : x - 1 / 2 = 0 := by
        nlinarith
      have hx1 : x = 1 / 2 := by linarith
      have hy1 : y = 1 / 2 := by
        nlinarith
      linarith
    · -- Backward: x = y implies equality holds
      intro heq
      have h6 : x = y := by linarith [ heq ]
      have h7 : y = 1 - x := by linarith
      rw [show y = (1: ℝ) - x by linarith]
      have h6 : (1 - x) = 1 - x := by linarith
      field_simp [(show (1 - x + 1 : ℝ) ≠ 0 by nlinarith), (show (x + 1 : ℝ) ≠ 0 by nlinarith)]
      <;> nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2) ]