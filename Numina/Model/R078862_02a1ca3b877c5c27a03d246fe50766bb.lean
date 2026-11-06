import Mathlib

theorem algebra_7783 (x y : ℤ) : 3*x^2-4*x*y+3*y^2=35 ↔
    (x=4 ∧ y=1) ∨ (x=1 ∧ y=4) ∨ (x=-4 ∧ y=-1) ∨ (x=-1 ∧ y=-4) := by
  constructor
  · -- Proof of the forward direction: if $(x, y)$ satisfies $3x^2-4xy+3y^2=35$, then it is one of the four possible solutions.
    rintro h
    have h1 : x ≤ 6 := by
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (x + 4 : ℤ), sq_nonneg (x + 1 : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (y - 4 : ℤ), sq_nonneg (y + 1 : ℤ), sq_nonneg (y + 4 : ℤ)]
    have h2 : x ≥ -6 := by
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (x + 4 : ℤ), sq_nonneg (x + 1 : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (y - 4 : ℤ), sq_nonneg (y + 1 : ℤ), sq_nonneg (y + 4 : ℤ)]
    have h3 : y ≤ 6 := by
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (x + 4 : ℤ), sq_nonneg (x + 1 : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (y - 4 : ℤ), sq_nonneg (y + 1 : ℤ), sq_nonneg (y + 4 : ℤ)]
    have h4 : y ≥ -6 := by
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (x + 4 : ℤ), sq_nonneg (x + 1 : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (y - 4 : ℤ), sq_nonneg (y + 1 : ℤ), sq_nonneg (y + 4 : ℤ)]
    interval_cases x <;> interval_cases y
    <;> omega
  · -- Proof of the reverse direction: each of the four possible solutions satisfies $3x^2-4xy+3y^2=35$.
    rintro (h | h | h | h)
    · -- Case $(4, 1)$
      rw [h.1, h.2]
      norm_num
    · -- Case $(1, 4)$
      rw [h.1, h.2]
      norm_num
    · -- Case $(-4, -1)$
      rw [h.1, h.2]
      norm_num
    · -- Case $(-1, -4)$
      rw [h.1, h.2]
      norm_num