import Mathlib

theorem algebra_9249 (x : ℝ) : (x - 2) * (x + 2) < 5 ↔ -3 < x ∧ x < 3 := by
  constructor
  · -- (→) direction: $(x-2)(x+2) < 5$ implies $-3 < x ∧ x < 3$
    intro h
    have h1 : x^2 < 9 := by
      nlinarith
    constructor
    · -- Proof of $-3 < x$
      nlinarith [h1, sq_nonneg (x + 3), sq_nonneg (x - 3)]
    · -- Proof of $x < 3$
      nlinarith [h1, sq_nonneg (x + 3), sq_nonneg (x - 3)]
  · -- (←) direction: $-3 < x ∧ x < 3$ implies $(x-2)(x+2) < 5$
    rintro ⟨h1, h2⟩
    have h3 : x^2 < 9 := by
      nlinarith [h1, h2, sq_nonneg (x - 3), sq_nonneg (x + 3)]
    nlinarith [h3, sq_nonneg (x - 3), sq_nonneg (x + 3)]