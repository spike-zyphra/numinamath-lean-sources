import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_12675 (a : ℝ) (ha : a ∈ Ioc (-2) 4) :
    ∀ x : ℝ, x^2 - a * x + 9 > 0 ↔ True := by
  rcases ha with ⟨ha1, ha2⟩
  intro x
  have h1 : x^2 - a * x + 9 > 0 := by
    nlinarith [sq_nonneg (x - a / 2), sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (x - a / 2 + 3)]
  constructor
  · -- Forward direction: If x^2 - a*x + 9 > 0, then True.
    intro h
    trivial
  · -- Backward direction: If True, then x^2 - a*x + 9 > 0.
    intro h
    linarith [h1]