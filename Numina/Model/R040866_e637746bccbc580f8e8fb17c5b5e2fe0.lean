import Mathlib

theorem algebra_178336 {a x y z : ℝ} (hx : x ≠ y) (hy : y ≠ z) (hz : x ≠ z) (h0: x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0) :
    (a + x) / (x * (x - y) * (x - z)) + (a + y) / (y * (y - z) * (y - x)) +
    (a + z) / (z * (z - x) * (z - y)) = a / (x * y * z) := by
  rcases h0 with ⟨hx0, hy0, hz0⟩
  have h1 : x - y ≠ 0 := by
    intro h
    apply hx
    linarith
  have h2 : y - z ≠ 0 := by
    intro h
    apply hy
    linarith
  have h3 : x - z ≠ 0 := by
    intro h
    apply hz
    linarith
  have h4 : y - x ≠ 0 := by
    intro h
    apply hx
    linarith
  have h5 : z - x ≠ 0 := by
    intro h
    apply hz
    linarith
  have h6 : z - y ≠ 0 := by
    intro h
    apply hy
    linarith
  field_simp [(show x ≠ 0 by exact hx0), (show y ≠ 0 by exact hy0), (show z ≠ 0 by exact hz0),
      show x - y ≠ 0 by exact h1, show y - z ≠ 0 by exact h2, show x - z ≠ 0 by exact h3,
      show y - x ≠ 0 by exact h4, show z - x ≠ 0 by exact h5, show z - y ≠ 0 by exact h6]
  ring