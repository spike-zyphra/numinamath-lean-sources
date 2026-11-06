import Mathlib

theorem algebra_316384 {x y z : ℝ} (h : 4 * x - 3 * y - 6 * z = 0) (h' : x + 2 * y - 7 * z = 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (5 * x ^ 2 + 2 * y ^ 2 - z ^ 2) / (2 * x ^ 2 - 3 * y ^ 2 - 10 * z ^ 2) = -13 := by
  have h1 : y = 2 * z := by
    linarith [h, h']
  have h2 : x = 3 * z := by
    linarith [h1, h']
  have eq1 : 5 * x ^ 2 + 2 * y ^ 2 - z ^ 2 = 52 * z ^ 2 := by
    rw [h2, h1]
    ring_nf
  have eq2 : 2 * x ^ 2 - 3 * y ^ 2 - 10 * z ^ 2 = -4 * z ^ 2 := by
    rw [h2, h1]
    ring_nf
  rw [eq1, eq2]
  have hz2 : z ^ 2 ≠ 0 := by
    apply pow_ne_zero 2 hz
  field_simp [hz2]
  <;> ring_nf <;> nlinarith