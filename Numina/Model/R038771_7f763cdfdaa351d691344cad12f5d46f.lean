import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_272394 (x : ℝ) :
  x ∈ Ioo (-3) 1 ↔ 0 < 3 - 2 * x - x ^ 2 := by
  constructor
  · -- Assume x ∈ (-3, 1), prove 0 < 3 - 2 * x - x ^ 2
    rintro ⟨hx1, hx2⟩
    have h1 : 3 - 2 * x - x ^ 2 > 0 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3)]
    linarith
  · -- Assume 0 < 3 - 2 * x - x ^ 2, prove x ∈ (-3, 1)
    intro h
    have h2 : -3 < x := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3)]
    have h3 : x < 1 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3)]
    constructor <;> linarith