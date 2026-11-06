import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_214184 (a : ℝ) :
  (∀ x ∈ Icc (-1) 1, a * x^2 + 2 * (a + 1) * x + a - 4 ≤ 0) ↔ a ≤ 1 / 2 := by
    constructor
    · -- Assume the inequality holds for all x ∈ [-1,1], prove a ≤ 1/2
      intro h
      have h1 := h 1 (by norm_num)
      nlinarith
    · -- Assume a ≤ 1/2, prove the inequality holds for all x ∈ [-1,1]
      intro ha x hx
      rcases hx with ⟨hx1, hx2⟩
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x * a), sq_nonneg (a - 1 / 2)]