import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_254185 (x : ℝ) (hx : x ≠ 1) : 1 / (x - 1) > 1 ↔ 1 < x ∧ x < 2 := by
  constructor
  · -- Assume $\frac{1}{x - 1} > 1$, prove $1 < x ∧ x < 2$.
    intro h
    have h1 : x - 1 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have h2 : 1 / (x - 1) - 1 > 0 := by linarith
    have h3 : (2 - x) / (x - 1) > 0 := by
      have pos : (1 / (x - 1) - 1) = (2 - x) / (x - 1) := by
        field_simp [h1]
        <;> ring
      linarith [pos, h2]
    apply div_pos_iff.mp at h3
    cases h3 with
    | inl h4 =>
      constructor
      · -- $1 < x$
        linarith
      · -- $x < 2$
        linarith
    | inr h4 =>
      exfalso
      linarith
  · -- Assume $1 < x ∧ x < 2$, prove $\frac{1}{x - 1} > 1$.
    rintro ⟨h1, h2⟩
    have h3 : x - 1 > 0 := by linarith
    have h4 : 2 - x > 0 := by linarith
    have h2' : (2 - x) / (x - 1) > 0 := by apply div_pos; all_goals linarith
    have h2 : 1 / (x - 1) - 1 > 0 := by
      have pos : (1 / (x - 1) - 1) = (2 - x) / (x - 1) := by
        field_simp [(show x - 1 ≠ 0 by
          by_contra h
          have : x = 1 := by linarith
          linarith
        )]
        <;> ring
      rw [pos]
      linarith
    linarith