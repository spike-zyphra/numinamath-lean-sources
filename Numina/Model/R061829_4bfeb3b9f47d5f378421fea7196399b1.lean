import Mathlib

theorem algebra_291001 (x : ℝ) (hx : 0 ≤ 3 * x - 2 - x ^ 2 ∧ 0 ≤ x ^ 2 - 4 * x + 3) :
    Real.sqrt (3 * x - 2 - x ^ 2) + Real.sqrt (x ^ 2 - 4 * x + 3) =
    Real.sqrt 2 * (1 - Real.sqrt x) ↔ x = 1 := by
  constructor
  · -- Forward direction: assume equality holds, prove $x = 1$.
    intro h_eq
    have h1 : 0 ≤ 3 * x - 2 - x^2 := hx.1
    have h2 : 0 ≤ x^2 - 4 * x + 3 := hx.2
    have h3 : 1 ≤ x := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 3)]
    have h4 : x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 3)]
    have h5 : x = 1 := by linarith
    exact h5
  · -- Backward direction: assume $x = 1$, prove equality holds.
    intro h_eq
    rw [h_eq]
    have h6 : Real.sqrt (3 * (1 : ℝ) - 2 - (1 : ℝ) ^ 2) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    have h7 : Real.sqrt (1 ^ 2 - 4 * (1 : ℝ) + 3) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    have h8 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    rw [h6, h7, h8]
    norm_num
    <;> ring_nf <;> norm_num