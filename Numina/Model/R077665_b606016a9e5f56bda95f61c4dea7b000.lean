import Mathlib

theorem algebra_94775 (x : ℝ) :
    (∃ y : ℝ, 4 * y ^ 2 + 4 * x * y + x + 6 = 0) ↔ x ≤ -2 ∨ x ≥ 3 := by
  constructor
  · -- Assume there exists y such that 4y² + 4xy + x + 6 = 0, prove x ≤ -2 or x ≥ 3
    rintro ⟨y, hy⟩
    have h1 : 16 * x ^ 2 - 16 * (x + 6) ≥ 0 := by
      nlinarith [sq_nonneg (4 * y + 2 * x)]
    have h2 : (x ^ 2 - x - 6) ≥ 0 := by
      nlinarith
    have h3 : (x ^ 2 - x - 6) = (x - 3) * (x + 2) := by
      ring
    rw [h3] at h2
    cases (mul_nonneg_iff.mp h2) with
    | inl h1 =>
      right
      linarith
    | inr h2 =>
      left
      nlinarith
  · -- Assume x ≤ -2 or x ≥ 3, prove there exists y real satisfying the equation
    rintro (h | h)
    · -- Case where x ≤ -2
      have h1 : (x ^ 2 - x - 6) ≥ 0 := by
        nlinarith [sq_nonneg (x + 2)]
      use (-4 * x + 4 * Real.sqrt (x ^ 2 - x - 6)) / 8
      nlinarith [Real.sqrt_nonneg (x ^ 2 - x - 6), Real.sq_sqrt (show (x ^ 2 - x - 6) ≥ 0 by nlinarith)]
    · -- Case where x ≥ 3
      have h1 : (x ^ 2 - x - 6) ≥ 0 := by
        nlinarith [sq_nonneg (x - 3)]
      use (-4 * x + 4 * Real.sqrt (x ^ 2 - x - 6)) / 8
      nlinarith [Real.sqrt_nonneg (x ^ 2 - x - 6), Real.sq_sqrt (show (x ^ 2 - x - 6) ≥ 0 by nlinarith)]