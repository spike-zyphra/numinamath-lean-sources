import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_284789 (a b : ℝ) (x : ℝ) :
  a^2 * x + b^2 * (1 - x) ≥ (a * x + b * (1 - x))^2 ↔ b = a ∨ x ∈ Icc 0 1 := by
  constructor
  · -- Assume the inequality holds, prove $b = a ∨ x \in Icc 0 1$
    intro h
    have h1 : a^2 * x + b^2 * (1 - x) - (a * x + b * (1 - x))^2 ≥ 0 := by nlinarith
    have h2 : x * (a - b) ^ 2 * (1 - x) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * x + b * (1 - x) - b), sq_nonneg (a * x + b * (1 - x) - a), sq_nonneg (x * (a - b)), sq_nonneg ((1 - x) * (a - b))]
    by_cases h3 : b = a
    · -- If b = a, then the inequality is trivial
      left
      exact h3
    · -- b ≠ a
      right
      have hb : b ≠ a := by
        intro h4
        apply h3
        linarith
      constructor
      · -- Show that 0 ≤ x
        nlinarith [sq_nonneg (x * (a - b)), sq_nonneg ((1 - x) * (a - b)), sq_pos_of_ne_zero (show a - b ≠ 0 by intro h0; apply hb; linarith)]
      · -- Show that x ≤ 1
        nlinarith [sq_nonneg (x * (a - b)), sq_nonneg ((1 - x) * (a - b)), sq_pos_of_ne_zero (show a - b ≠ 0 by intro h0; apply hb; linarith)]
  · -- Assume $b = a ∨ x \in Icc 0 1$, prove the inequality
    intro h
    cases h with
    | inl h_eq =>
      rw [show b = a by linarith]
      nlinarith
    | inr h2 =>
      rcases h2 with ⟨hx1, hx2⟩
      have h1 : x * (a - b) ^ 2 * (1 - x) ≥ 0 := by
        have h2 : x ≥ 0 := by
          linarith [hx1]
        have h3 : 1 - x ≥ 0 := by
          linarith [hx2]
        have h4 : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
        have h5 : x * (a - b) ^ 2 ≥ 0 := mul_nonneg h2 h4
        have h6 : x * (a - b) ^ 2 * (1 - x) ≥ 0 := mul_nonneg h5 h3
        linarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * x + b * (1 - x) - b), sq_nonneg (a * x + b * (1 - x) - a), sq_nonneg (x * (a - b)), sq_nonneg ((1 - x) * (a - b))]