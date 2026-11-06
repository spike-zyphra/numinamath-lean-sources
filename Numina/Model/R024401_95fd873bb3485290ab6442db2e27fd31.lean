import Mathlib

theorem inequalities_240589 (a : ℝ) :
    (∀ x y, 2 * a * x ^ 2 + 2 * a * y ^ 2 + 4 * a * x * y - 2 * x * y - y ^ 2 - 2 * x + 1 ≥ 0) ↔
    a ≥ 1 / 2 := by
  constructor
  · -- Assume that for all x, y, the inequality holds, then a ≥1/2
    intro h
    have h1 : ∀ x, 2 * a * x ^ 2 - 2 * x + 1 ≥ 0 := by
      intro x
      specialize h x 0
      linarith
    have h5 := h1 1
    nlinarith
  · -- Assume $a \geq1/2$ then the inequality holds
    intro ha x y
    have h1: 2 * a * x ^ 2 + 2 * a * y ^ 2 + 4 * a * x * y - 2 * x * y - y ^ 2 - 2 * x + 1 ≥ 0 :=
      by
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (x -1), sq_nonneg (x + 2 * a * y -1), sq_nonneg (2 * a * (x + y) -1), sq_nonneg ((x + y)), sq_nonneg ((x - (y)) ), sq_nonneg ((y - 0)), sq_nonneg ((x -1)), sq_nonneg ((y)), sq_nonneg ((x + 2*y*a)), sq_nonneg ((a -1/2)), sq_nonneg ((x - 1 / a) ), sq_nonneg (y -0), sq_nonneg (x -1), sq_nonneg ((y - x)), sq_nonneg ((x - (a-1)) ), sq_nonneg (x - 1 / (2 * a)), sq_nonneg (2*a), mul_nonneg (show 0 ≤ (a - 1 / 2) by linarith) (show 0 ≤ 2 * a by linarith), sq_nonneg (x * (2*a) ), sq_nonneg (y * (2 * a) )
          ]
    linarith