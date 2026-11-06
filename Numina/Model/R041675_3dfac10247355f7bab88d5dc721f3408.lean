import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_192208 (p : ℝ) :
  (∃ x y, p = x + y ∧ x^2 + 4 * y^2 + 8 * y + 4 ≤ 4 * x) ↔
  1 - sqrt 5 ≤ p ∧ p ≤ 1 + sqrt 5 := by
  constructor
  · -- Assume there exists x, y such that p = x + y and the inequality
    rintro ⟨x, y, hp, h⟩
    have h1 : (x - 2) ^ 2 + 4 * (y + 1) ^ 2 ≤ 4 := by
      nlinarith
    have h3 : 1 - Real.sqrt 5 ≤ p := by
      nlinarith [sq_nonneg (x - (2 + 4 * y + 4)), sq_nonneg (y + 1), 
        Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
        sq_nonneg (p - (1 - Real.sqrt 5)), sq_nonneg (p - (1 + Real.sqrt 5))]
    have h4 : p ≤ 1 + Real.sqrt 5 := by
      nlinarith [sq_nonneg (x - (2 + 4 * y + 4)), sq_nonneg (y + 1), 
        Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
        sq_nonneg (p - (1 - Real.sqrt 5)), sq_nonneg (p - (1 + Real.sqrt 5))]
    constructor
    · -- Prove the left part of the conjunction
      linarith [h3]
    · -- Prove the right part of the conjunction
      linarith [h4]
  · -- Assume the bounds on p
    rintro ⟨hp1, hp2⟩
    use (4 * p + 6) / 5, (p - 6) / 5
    constructor
    · -- Show that p = x + y
      linarith
    · -- Show the inequality
      nlinarith [Real.sqrt_nonneg 5, 
        Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
        sq_nonneg (p - (1 - Real.sqrt 5)), sq_nonneg (p - (1 + Real.sqrt 5)), 
        mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5)]