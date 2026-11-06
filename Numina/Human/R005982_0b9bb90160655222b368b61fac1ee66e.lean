import Mathlib

open Polynomial

/- A manufacturer of airplane parts makes a certain engine that has a probability $p$ of failing on any given flight. Their are two planes that can be made with this sort of engine, one that has 3 engines and one that has 5. A plane crashes if more than half its engines fail. For what values of $p$ do the two plane models have the same probability of crashing? -/
theorem number_theory_610966 : ∀ p : ℝ, 0 ≤ p ∧ p ≤ 1 →
    ((Nat.choose 5 2) * p^3 * (1-p)^2 + (Nat.choose 5 1) * p^4 * (1-p) + p^5
  = (Nat.choose 3 1) * p^2 * (1-p) + p^3
  ↔ p ∈ ({0, 1/2, 1} : Set ℝ)) :=
by
  simp [Nat.choose]
  ring_nf
  intros p l r
  constructor
  intro eq
  -- Retrieve the original equation
  have :  6 * p^5 - 15 * p^4 + 12 * p^3 - 3 * p^2 = 0 := by
    have : p^3 * 10 - p^4 * 15 + p^5 * 6 + p^3 * 2 = p^2 * 3 := by
      linarith[eq]
    have : - p^2 * 3 + p^3 * 12 - p^4 * 15 + p^5 * 6 = 0 := by
      linarith[this]
    linarith[this]
  -- Solve the equation using factorization
  have fact_eq : p^2 * (p - 1)^2 * (2 * p - 1) * 3 = 0 := by
    ring_nf
    linarith[this]
  simp at fact_eq
  rcases fact_eq with (h|h)
  . rcases h with (h|h)
    . left; assumption
    . right; right;
      linarith
  . right; left
    linarith
  -- mpr case, simply verify each value.
  intros h
  rcases h with (h|h)
  . simp[h]
  . rcases h with (h|h)
    . rw[h]
      linarith
    . rw[h]
      linarith
