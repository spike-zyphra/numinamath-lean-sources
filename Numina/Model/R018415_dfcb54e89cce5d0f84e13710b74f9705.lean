import Mathlib

theorem algebra_296529 (p q : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + p * x + q)
    (h : 1 + p + q < 0) :
    ∃ x, x > 1 ∧ f x = 0 ∧ ∃ x, x < 1 ∧ f x = 0 := by

  have h1 : f 1 < 0 := by
    rw [hf]
    nlinarith

  have h3 : p ^ 2 - 4 * q > 0 := by
    nlinarith [sq_nonneg (p + 2), sq_nonneg (1 + p + q), sq_nonneg (p), sq_nonneg (q)]

  use (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2

  constructor
  · -- Show that x > 1
    nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by nlinarith)]
  constructor
  · -- Show that f x = 0
    rw [hf]
    nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by nlinarith)]
  · -- Show that ∃ x, x < 1 ∧ f x = 0
    use (-p - Real.sqrt (p ^ 2 - 4 * q)) / 2
    constructor
    · -- Show that x < 1
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by nlinarith)]
    · -- Show that f x = 0
      rw [hf]
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by nlinarith)]