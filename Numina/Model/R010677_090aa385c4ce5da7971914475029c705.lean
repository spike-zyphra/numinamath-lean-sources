import Mathlib

theorem algebra_9190 (x : ℝ) : 2 * x ^ 2 - x ≤ 0 ↔ 0 ≤ x ∧ x ≤ 1 / 2 := by
  constructor
  · -- First direction: if $2x^2 - x \leq 0$ then $0 \leq x \wedge x \leq \frac{1}{2}$
    intro h
    have h1 : 2 * x ^ 2 - x ≤ 0 := h
    have h2 : x * (2 * x - 1) ≤ 0 := by
      nlinarith
    cases mul_nonpos_iff.mp h2 with
    | inl h3 =>
      constructor
      · linarith
      · linarith
    | inr h4 =>
      linarith
  · -- Second direction: if $0 \leq x \wedge x \leq \frac{1}{2}$ then $2x^2 - x \leq 0$
    rintro ⟨hx1, hx2⟩
    have h2 : 2 * x ^ 2 - x ≤ 0 := by
      nlinarith
    linarith