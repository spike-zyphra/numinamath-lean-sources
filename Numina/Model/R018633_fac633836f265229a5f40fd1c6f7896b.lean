import Mathlib

theorem algebra_656 {x : ℝ} (hx : x + 1 ≠ 0) : (3 / (x + 1)) - 4 = (3 - 4 / (x + 1)) ↔ x = 0 := by
  constructor
  · -- Assume the equation holds, prove x = 0
    intro h
    have h1 : (3 / (x + 1)) - 4 = (3 - 4 / (x + 1)) := h
    have h2 : x + 1 ≠ 0 := hx
    have eq1 : 3 - 4 * (x + 1) = 3 * (x + 1) - 4 := by
      have eq2 : (3 / (x + 1) - 4) * (x + 1) = (3 - 4 / (x + 1)) * (x + 1) := by
        rw [h1]
      have eq4 : (3 / (x + 1) - 4) * (x + 1) = 3 - 4 * (x + 1) := by
        field_simp [h2]
        <;> ring_nf
      have eq5 : (3 - 4 / (x + 1)) * (x + 1) = 3 * (x + 1) - 4 := by
        field_simp [h2]
        <;> ring_nf
      rw [eq4, eq5] at eq2
      linarith
    have eq2 : x = 0 := by
      linarith
    exact eq2
  · -- Assume x = 0, prove the equation
    intro h
    rw [h]
    norm_num
    <;> ring_nf
    <;> norm_num