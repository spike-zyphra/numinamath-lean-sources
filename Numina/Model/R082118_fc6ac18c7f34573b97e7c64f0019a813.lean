import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_274743 :
  IsLeast {x | ∃ a b c d : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a + b + c + d = sqrt 7960 ∧ x = a^2 + b^2 + c^2 + d^2} 1990 := by
  constructor
  · -- Show 1990 is in the set
    use Real.sqrt 1990 / 2, Real.sqrt 1990 / 2, Real.sqrt 1990 / 2, Real.sqrt 1990 / 2
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · -- Show that the sum is sqrt(7960)
      have h1 : Real.sqrt 7960 = 2 * Real.sqrt 1990 := by
        calc
          Real.sqrt 7960 = Real.sqrt (2^2 * 1990) := by norm_num
          _ = (Real.sqrt (2^2)) * Real.sqrt 1990 := by rw [Real.sqrt_mul (by norm_num)]
          _ = (2) * Real.sqrt 1990 := by rw [Real.sqrt_sq (by norm_num)]
          _ = 2 * Real.sqrt 1990 := by ring
      linarith [h1]
    · -- Show that x = a^2 + b^2 + c^2 + d^2
      nlinarith [Real.sq_sqrt (show 0 ≤ 1990 by norm_num)]
  · -- Show that 1990 is the least element
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, hsum, hx⟩
    have h1 : (a + b + c + d)^2 ≤ 4*(a^2 + b^2 + c^2 + d^2) := by
      linarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    have h2 : (Real.sqrt 7960)^2 ≤ 4*(a^2 + b^2 + c^2 + d^2) := by
      have h3 : (a + b + c + d) = Real.sqrt 7960 := hsum
      rw [h3] at h1
      nlinarith
    have h3 : (Real.sqrt 7960)^2 = 7960 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    nlinarith [h3, hx]