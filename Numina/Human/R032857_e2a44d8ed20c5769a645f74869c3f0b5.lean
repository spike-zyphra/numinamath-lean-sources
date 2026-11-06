import Mathlib

open Real

theorem inequalities_6511 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    x^2 < x ∧ (x^2 < x ↔ 0 < x ∧ x < 1) ∧ (x^2 > x → x > 1) := by
  constructor
  · -- $x^2 < x$ if $0 < x < 1$
    nlinarith
  constructor
  · -- $x^2 < x$ if and only if $0 < x < 1$
    constructor
    · -- $x^2 < x \implies 0 < x < 1$
      intro h
      constructor
      · -- $x > 0$
        nlinarith [sq_nonneg x]
      · -- $x < 1$
        by_contra!
        nlinarith [sq_nonneg (x - 1)]
    · -- $0 < x < 1 \implies x^2 < x$ (already proved as the first statement)
      rintro ⟨hx1, hx2⟩
      nlinarith
  · -- If $x^2 > x$, then $x > 1$
    intro h
    nlinarith [sq_nonneg (x - 1)]