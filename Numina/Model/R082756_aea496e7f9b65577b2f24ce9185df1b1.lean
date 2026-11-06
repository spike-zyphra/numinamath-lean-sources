import Mathlib

theorem algebra_95325 (f : ℝ → ℝ) (hf : f = fun x => (2 * x ^ 2 - x) / ((x + 1) * (x - 2)) - (4 + x) / ((x + 1) * (x - 2))) :
    ∀ x, x ≠ -1 ∧ x ≠ 2 → f x = 2 := by
  intro x h
  have h1 : x ≠ -1 := h.1
  have h2 : x ≠ 2 := h.2
  rw [hf]
  have denom_ne_zero : (x + 1) * (x - 2) ≠ 0 := by
    apply mul_ne_zero
    · -- Show x + 1 ≠ 0, so x ≠ -1
      intro h
      apply h1
      linarith
    · -- Show x - 2 ≠ 0, so x ≠ 2
      intro h
      apply h2
      linarith
  field_simp [(show (x + 1) * (x - 2) ≠ 0 by exact denom_ne_zero)]
  <;> ring