import Mathlib

theorem algebra_194147 {x y z : ℝ} (hy : y ≠ -z) (hz : z ≠ -x) (hx : x ≠ -y)
    (h : x / (y + z) + y / (z + x) + z / (x + y) = 1) :
    x ^ 2 / (y + z) + y ^ 2 / (z + x) + z ^ 2 / (x + y) = 0 := by

  have h1 : y + z ≠ 0 := by
    intro h'
    apply hy
    linarith
  have h2 : z + x ≠ 0 := by
    intro h'
    apply hz
    linarith
  have h3 : x + y ≠ 0 := by
    intro h'
    apply hx
    linarith

  have eq1 : x ^ 2 / (y + z) + y ^ 2 / (z + x) + z ^ 2 / (x + y) =
      (x + y + z) * (x / (y + z) + y / (z + x) + z / (x + y)) - (x + y + z) := by 
    field_simp [h1, h2, h3]
    ring

  rw [eq1]
  rw [h]
  ring