import Mathlib

theorem algebra_4082 (x y : ℝ) (hx : x ≠ 1) : x * y = x + y ↔ (x, y) = (x, x / (x - 1)) := by
  constructor
  · -- Forward direction: if $xy = x + y$, then $y = x / (x - 1)$ given that $x \ne 1$
    intro h_eq
    have h1 : x - 1 ≠ 0 := by
      intro h
      apply hx
      linarith
    have h2 : y = x / (x - 1) := by
      field_simp [h1]
      linarith
    exact Prod.ext rfl h2
  · -- Backward direction: if $y = x / (x - 1)$ and $x \ne 1$, then $xy = x + y$
    rintro ⟨rfl, rfl⟩
    have h1 : x - 1 ≠ 0 := by
      intro h
      apply hx
      linarith
    field_simp [h1]
    <;> ring