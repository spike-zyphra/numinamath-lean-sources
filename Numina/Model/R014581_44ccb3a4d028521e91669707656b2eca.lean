import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_323344 (m : ℝ) :
  (∃ x y : ℝ, x ≥ 0 ∧ y = m * (x + 2) - 4 ∧ x ^ 2 + y ^ 2 = 4) ↔
  3 / 4 ≤ m ∧ m ≤ 3 := by
  constructor
  · -- Forward implication: if there's a solution, then 3/4 ≤ m ≤ 3
    rintro ⟨x, y, hx, hy, heq⟩
    have h1 : x ^ 2 + (m * (x + 2) - 4) ^ 2 = 4 := by
      rw [show y = m * (x + 2) - 4 by linarith [hy]] at heq
      linarith
    have h2 : m ≥ 3 / 4 := by
      nlinarith [sq_nonneg (x * m - (m * (x + 2) - 4)), sq_nonneg (x - 6 / 5), sq_nonneg (m * x - 3 * x), sq_nonneg (y - (-8 / 5)), sq_nonneg (x * m), sq_nonneg (m - 3 / 4), sq_nonneg (m - 3), sq_nonneg (x - 0), sq_nonneg (x - 6 / 5), sq_nonneg (y - 2)]
    have h3 : m ≤ 3 := by
      nlinarith [sq_nonneg (x * m - (m * (x + 2) - 4)), sq_nonneg (x - 6 / 5), sq_nonneg (m * x - 3 * x), sq_nonneg (y - (-8 / 5)), sq_nonneg (x * m), sq_nonneg (m - 3 / 4), sq_nonneg (m - 3), sq_nonneg (x - 0), sq_nonneg (x - 6 / 5), sq_nonneg (y - 2), mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ (4 - x^2) by nlinarith [heq]) ]
    constructor
    · linarith
    · linarith
  · -- Backward direction: if 3/4 ≤ m ≤ 3, then there's a solution
    rintro ⟨hm1, hm2⟩
    have h4 : m ≥ 3 / 4 := by linarith
    have h5 : m ≤ 3 := by linarith
    have h9 : 0 ≤ 64 * m - 48 := by nlinarith
    have h8 : 0 ≤ Real.sqrt (64 * m - 48) := Real.sqrt_nonneg (64 * m - 48)
    use (-4 * m ^ 2 + 8 * m + Real.sqrt (64 * m - 48)) / (2 * (1 + m ^ 2))
    use m * ((-4 * m ^ 2 + 8 * m + Real.sqrt (64 * m - 48)) / (2 * (1 + m ^ 2)) + 2) - 4
    constructor
    · -- Show x ≥ 0
      apply div_nonneg
      · -- Show -4 * m ^ 2 + 8 * m + Real.sqrt (64 * m - 48) ≥ 0
        nlinarith [Real.sqrt_nonneg (64 * m - 48), Real.sq_sqrt (show (0 : ℝ) ≤ (64 * m - 48) by nlinarith), sq_nonneg (Real.sqrt (64 * m - 48) - 12), sq_nonneg (m - 3 / 4), sq_nonneg (m - 3)
        ]
      · -- Show 2 * (1 + m ^ 2) ≥ 0
        positivity
    constructor
    · -- Show y = m * (x + 2) - 4
      rfl
    · -- Show x ^ 2 + y ^ 2 = 4
      field_simp
      nlinarith [Real.sqrt_nonneg (64 * m - 48), Real.sq_sqrt (show (0 : ℝ) ≤ (64 * m - 48) by nlinarith), sq_nonneg (m - 3 / 4), sq_nonneg (m - 3), sq_nonneg (m - 1), sq_nonneg (Real.sqrt (64 * m - 48) - 0), Real.sq_sqrt (show (0 : ℝ) ≤ (64 * m - 48) by nlinarith)
      ]