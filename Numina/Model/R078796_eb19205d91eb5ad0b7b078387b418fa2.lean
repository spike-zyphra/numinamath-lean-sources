import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_304827 (a : ℝ) :
  ¬ (∃ x : ℝ, x - 1 > 0 ∧ x - a < 0) ↔ a ≤ 1 := by
  constructor
  · -- Assume the system has no solution, prove a ≤ 1
    intro h
    by_contra h1
    push_neg at h1
    have h3 : ∃ x : ℝ, x - 1 > 0 ∧ x - a < 0 := by
      use (a + 1) / 2
      constructor
      · -- $x - 1 > 0$ becomes $(a + 1)/2 - 1 > 0$ which simplifies to $(a - 1)/2 > 0$
        linarith
      · -- $(a + 1)/2 - a < 0$ becomes $(a + 1 - 2a)/2 < 0$, which simplifies to $(1 - a)/2 < 0$
        linarith
    contradiction
  · -- Assume a ≤ 1, prove the system has no solution
    intro h
    intro h1
    rcases h1 with ⟨x, hx1, hx2⟩
    linarith