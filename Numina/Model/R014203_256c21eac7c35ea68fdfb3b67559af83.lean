import Mathlib

theorem algebra_304310 (m : ℝ) :
    (∃ x y, y = x ^ 2 ∧ x ^ 2 + (y - m) ^ 2 = 1) ↔ m ∈ Set.Icc (-1) (5 / 4) := by
  constructor
  · -- Forward implication: if there's a common point (x, y), then -1 ≤ m ≤ 5/4
    rintro ⟨x, y, hy, h⟩
    rw [hy] at h
    have h3 : m ≤ 5 / 4 := by
      nlinarith [sq_nonneg (x ^ 2 - (m - 1 / 2)), sq_nonneg (x ^ 2 - m), sq_nonneg (x ^ 2 - 1 / 2)]
    have h4 : m ≥ -1 := by
      nlinarith [sq_nonneg (x ^ 2 - m), sq_nonneg (x ^ 2 - m + 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 2)]
    constructor <;> linarith
  · -- Backward implication: if m ∈ [-1, 5/4], then there's a common point (x, y)
    rintro ⟨hm1, hm2⟩
    use Real.sqrt ((2 * m - 1 + Real.sqrt (5 - 4 * m)) / 2)
    use (2 * m - 1 + Real.sqrt (5 - 4 * m)) / 2
    constructor
    · -- Show that y = x^2
      have hx : (Real.sqrt ((2 * m - 1 + Real.sqrt (5 - 4 * m)) / 2)) ^ 2 = (2 * m - 1 + Real.sqrt (5 - 4 * m)) / 2 := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg (5 - 4 * m), Real.sq_sqrt (show 0 ≤ 5 - 4 * m by nlinarith), sq_nonneg (Real.sqrt (5 - 4 * m) - 2)]
      linarith
    · -- Show that x^2 + (y - m) ^ 2 = 1
      have hx : (Real.sqrt ((2 * m - 1 + Real.sqrt (5 - 4 * m)) / 2)) ^ 2 = (2 * m - 1 + Real.sqrt (5 - 4 * m)) / 2 := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg (5 - 4 * m), Real.sq_sqrt (show 0 ≤ 5 - 4 * m by nlinarith), sq_nonneg (Real.sqrt (5 - 4 * m) - 2)]
      nlinarith [Real.sqrt_nonneg (5 - 4 * m), Real.sq_sqrt (show 0 ≤ 5 - 4 * m by nlinarith), sq_nonneg (Real.sqrt (5 - 4 * m) - 2), Real.sqrt_nonneg ((2 * m - 1 + Real.sqrt (5 - 4 * m)) / 2)]