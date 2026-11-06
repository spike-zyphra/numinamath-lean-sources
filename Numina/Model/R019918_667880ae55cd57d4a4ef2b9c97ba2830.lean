import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_321675 {p : ℝ} (hp : p > 0) (A B : ℝ × ℝ)
  (hA : A.2^2 = 2 * p * A.1) (hB : B.2^2 = 2 * p * B.1)
  (hAB : A ≠ B) :
  IsLeast {x | ∃ A B : ℝ × ℝ, A.2^2 = 2 * p * A.1 ∧ B.2^2 = 2 * p * B.1 ∧ A ≠ B ∧ x = (A.1 + B.1)^2 + (A.2 + B.2)^2 - (A.1 - B.1)^2 - (A.2 - B.2)^2} (-4 * p^2) := by

  constructor
  · -- Show that -4 * p^2 is in the set
    use (p / 2, p), (2 * p, -2 * p)
    constructor
    · -- Check that A is on the parabola
      ring_nf
    constructor
    · -- Check that B is on the parabola
      ring_nf
    constructor
    · -- Check that A ≠ B
      by_contra h
      have h1 : p / 2 = 2 * p := by
        simpa using congrArg Prod.fst h
      nlinarith
    · -- Verify the value of the expression
      ring_nf
  · -- Show that for any x in the set, x ≥ -4 * p^2
    intro x hx
    rcases hx with ⟨A, B, hA, hB, hAB, hx⟩
    have eq1 : (A.1 + B.1) ^ 2 + (A.2 + B.2) ^ 2 - (A.1 - B.1) ^ 2 - (A.2 - B.2) ^ 2 = 4 * (A.1 * B.1 + A.2 * B.2) := by
      ring
    have eq5 : A.1 * B.1 + A.2 * B.2 ≥ -p ^ 2 := by
      have eq6 : A.1 = A.2^2 / (2 * p) := by
        have hp2 : p ≠ 0 := by linarith
        field_simp [hp2]
        <;> nlinarith
      have eq7 : B.1 = B.2^2 / (2 * p) := by
        have hp2 : p ≠ 0 := by linarith
        field_simp [hp2]
        <;> nlinarith
      have eq8 : A.1 * B.1 + A.2 * B.2 = ((A.2 * B.2) ^ 2) / (4 * p^2) + (A.2 * B.2) := by
        rw [eq6, eq7]
        field_simp [(show p ≠ 0 by linarith)]
        <;> ring
      have eq9 : ((A.2 * B.2) ^ 2) / (4 * p^2) + (A.2 * B.2) ≥ -p ^ 2 := by
        have eq10 : ((A.2 * B.2) ^ 2) / (4 * p^2) + (A.2 * B.2) + p ^ 2 ≥ 0 := by
          have eq11 : ((A.2 * B.2) ^ 2) / (4 * p^2) + (A.2 * B.2) + p ^ 2 = ((A.2 * B.2 + 2 * p^2) ^ 2) / (4 * p^2) := by
            field_simp [(show p ≠ 0 by linarith)]
            <;> ring
          rw [eq11]
          apply div_nonneg
          · -- Show the numerator is non-negative
            apply pow_two_nonneg
          · -- Show the denominator is non-negative
            positivity
        linarith
      linarith [eq8, eq9]
    have eq11 : (A.1 + B.1) ^ 2 + (A.2 + B.2) ^ 2 - (A.1 - B.1) ^ 2 - (A.2 - B.2) ^ 2 ≥ -4 * p^2 := by
      linarith [eq1, eq5]
    linarith [hx, eq11]