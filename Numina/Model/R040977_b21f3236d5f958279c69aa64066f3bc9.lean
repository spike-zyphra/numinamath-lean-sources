import Mathlib
theorem algebra_233334 (n : ℚ) (h : n + 3 ≠ 0):
  n / (n + 1 - (n + 2) / (n + 3)) = (n ^ 2 + 3 * n) / (n ^ 2 + 3 * n + 1) ∧
  (n ^ 2 + 3 * n + 1) - (n ^ 2 + 3 * n) = 1 := by
  constructor
  · -- Show the original expression equals the simplified fraction.
    have h1 : n + 3 ≠ 0 := h
    have eq1 : n / (n + 1 - (n + 2) / (n + 3)) = (n ^ 2 + 3 * n) / (n ^ 2 + 3 * n + 1) := by
      have eq2 : n + 1 - (n + 2) / (n + 3) = (n ^ 2 + 3 * n + 1) / (n + 3) := by
        field_simp [h1]
        <;> ring
      rw [eq2]
      field_simp [h1]
      <;> ring
    exact eq1
  · -- Show the difference is 1.
    ring_nf