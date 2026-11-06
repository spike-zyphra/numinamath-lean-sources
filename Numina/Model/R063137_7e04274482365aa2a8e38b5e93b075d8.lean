import Mathlib

theorem algebra_94995 (x : ℝ) (hx : x ≠ 0 ∧ x ≠ 5) :
    (2 * x ^ 2 - 10 * x) / (x ^ 2 - 5 * x) = x - 3 ↔ False := by

  have h1 : x^2 - 5 * x = x * (x - 5) := by ring

  have h2 : 2 * x^2 - 10 * x = 2 * x * (x - 5) := by ring

  have h3 : (2 * x ^ 2 - 10 * x) / (x ^ 2 - 5 * x) = 2 := by
    rw [h1, h2]
    have hx1 : x ≠ 0 := hx.1
    have hx2 : x - 5 ≠ 0 := by
      intro h
      apply hx.2
      linarith
    field_simp [hx1, hx2]
    <;> ring

  rw [h3]

  constructor
  · -- Assume 2 = x - 3, we need to prove False
    intro h
    have h4 : x = 5 := by linarith
    have h5 : x ≠ 5 := hx.2
    contradiction

  · -- Assume False, we need to prove 2 = x - 3
    intro h
    cases h