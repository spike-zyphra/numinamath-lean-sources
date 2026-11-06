import Mathlib

theorem algebra_274715 {x y z : ℝ} (hy : y ≠ z) (h : (x - y) / (z - y) = -10) :
    (x - z) / (y - z) = 11 := by
  have h1 : z - y ≠ 0 := by
    intro h2
    have h3 : y = z := by linarith
    contradiction
  have h2 : x - y = -10 * (z - y) := by
    field_simp [h1] at h
    linarith
  have h3 : x - z = -11 * (z - y) := by
    linarith [h2]
  have h4 : y - z ≠ 0 := by
    intro h2
    have h3 : y = z := by linarith
    contradiction
  have h5 : (x - z) / (y - z) = 11 := by
    rw [h3]
    field_simp [h4]
    <;> ring
  exact h5