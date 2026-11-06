import Mathlib

theorem number_theory_2623 (a b c : ℤ) : c^2 = a^2 + b^2 + a * b ↔ (2 * c)^2 = (2 * a + b)^2 + 3 * b^2 := by
  constructor
  · -- Assume $c^2 = a^2 + b^2 + a * b$ and prove $(2 * c)^2 = (2 * a + b)^2 + 3 * b^2$
    intro h
    have h1 : (2 * c) ^ 2 = (2 * a + b) ^ 2 + 3 * b^2 := by
      nlinarith [h]
    exact h1
  · -- Assume $(2 * c)^2 = (2 * a + b)^2 + 3 * b^2$ and prove $c^2 = a^2 + b^2 + a * b$
    intro h
    have h1 : c^2 = a^2 + b^2 + a * b := by
      nlinarith [h]
    exact h1