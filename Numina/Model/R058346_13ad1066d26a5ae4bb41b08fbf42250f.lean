import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_256175 (a : ℝ) :
  (∀ x y : ℝ, (x - y ≤ 0 ∧ x + y - 5 ≥ 0 ∧ y - 3 ≤ 0) → a * (x^2 + y^2) ≤ (x + y)^2) ↔
  a ≤ 25 / 13 := by
  constructor
  · -- Assume that inequality holds
    intro h
    have h1 := h 2 3 (by norm_num)
    nlinarith
  · -- Assume a ≤ 25/13, show inequality holds
    intro ha x y h
    rcases h with ⟨h1, h2, h3⟩
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (x - y), sq_nonneg (x + y - 5),
      sq_nonneg (y - 3), sq_nonneg (x * 2 + y * 3 - 5), sq_nonneg (y - 2), sq_nonneg (x), sq_nonneg (y - 3)]