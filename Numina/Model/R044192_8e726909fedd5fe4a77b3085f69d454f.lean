import Mathlib

theorem algebra_199714 {x y z k1 k2 : ℝ} (hxy : x ≠ 0 ∧ y ≠ 0)
    (h1 : y - z = k1 * x) (h2 : z - x = k2 * y) (h3 : k1 ≠ k2)
    (h4 : z = 3 * (x - y)) :
    (k1 + 3) * (k2 + 3) = 8 := by
  rcases hxy with ⟨hx, hy⟩
  have eq1 : y - z = k1 * x := h1
  rw [h4] at eq1
  have eq2 : z - x = k2 * y := h2
  rw [h4] at eq2
  have eq3 : 4 * y = (k1 + 3) * x := by
    linarith
  have eq4 : 2 * x = (k2 + 3) * y := by
    linarith
  have eq5 : 8 * (x * y) = (k1 + 3) * (k2 + 3) * (x * y) := by
    have eq6 : 4 * y = (k1 + 3) * x := eq3
    have eq7 : 2 * x = (k2 + 3) * y := eq4
    calc
      8 * (x * y) = (4 * y) * (2 * x) := by
        ring
      _ = ((k1 + 3) * x) * ((k2 + 3) * y) := by
        rw [eq6, eq7]
      _ = (k1 + 3) * (k2 + 3) * (x * y) := by
        ring
  have h5 : x * y ≠ 0 := by
    apply mul_ne_zero
    exact hx
    exact hy
  have eq8 : (k1 + 3) * (k2 + 3) = 8 := by
    apply (mul_left_inj' h5).mp
    linarith
  linarith