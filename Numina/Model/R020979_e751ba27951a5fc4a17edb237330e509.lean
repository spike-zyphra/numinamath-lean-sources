import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303473 :
  IsLeast {x | ∃ a b c : ℝ, x = a * b + b * c + c * a ∧ a ^ 2 + b ^ 2 = 1 ∧ b ^ 2 + c ^ 2 = 2 ∧ c ^ 2 + a ^ 2 = 2} (-Real.sqrt 3 + 1 / 2) := by
  constructor
  · -- Show that -sqrt(3) + 1/2 is achievable
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2, -Real.sqrt 6 / 2
    constructor
    · -- Show that $ab + bc + ca = -sqrt(3) + 1/2$
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)
      have h3 : Real.sqrt 2 * Real.sqrt 6 = Real.sqrt 12 := by
        calc
          Real.sqrt 2 * Real.sqrt 6 = Real.sqrt (2 * 6) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 12 := by norm_num
      have h4 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sqrt_nonneg 3]
    constructor
    · -- Show that a^2 + b^2 = 1
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      nlinarith [h1, Real.sqrt_nonneg 2]
    constructor
    · -- Show that b^2 + c^2 = 2
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)
      nlinarith [h1, h2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6]
    · -- Show that c^2 + a^2 = 2
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)
      nlinarith [h1, h2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6]
  · -- Show that -sqrt(3) + 1/2 is the minimum
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2, h3, h4⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (b + c), sq_nonneg (c + a), sq_nonneg (a - Real.sqrt 2 / 2), sq_nonneg (b - Real.sqrt 2 / 2), sq_nonneg (c + Real.sqrt 6 / 2), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]