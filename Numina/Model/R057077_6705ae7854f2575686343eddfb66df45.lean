import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_199699 (m : ℝ) :
  (∀ x : ℝ, x^2 + (m + 2)*x + 8*m + 1 > 0) ↔ m > 0 ∧ m < 28 := by 
  constructor
  · -- Assume that for all real $x$, $x^2 + (m + 2) x + 8 m + 1 > 0$; prove $0 < m \land m < 28$.
    intro h
    have h1 := h (- (m + 2) / 2)
    have h2 : m^2 - 28 * m < 0 := by
      nlinarith [h1]
    constructor
    · -- Prove $m > 0$
      nlinarith
    · -- Prove $m < 28$
      nlinarith
  · -- Assume $0 < m \land m < 28$; prove $\forall x : \mathbb{R}, x^2 + (m + 2) x + 8 m + 1 > 0$
    rintro ⟨h1, h2⟩
    intro x
    have h3 : m^2 - 28 * m < 0 := by nlinarith
    nlinarith [sq_nonneg (x + (m + 2) / 2)]