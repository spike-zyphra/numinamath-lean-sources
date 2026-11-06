import Mathlib

theorem algebra_322595 (x y z : ℝ) (h1 : 4 * x - 3 * y - 6 * z = 0) (h2 : x + 2 * y - 7 * z = 0)
    (h3 : x * y * z ≠ 0) :
    (2 * x ^ 2 + 3 * y ^ 2 + 6 * z ^ 2) / (x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2) = 1 := by
  have hy : y = 2 * z := by
    nlinarith [h1, h2]
  have hx : x = 3 * z := by
    rw [hy] at h2
    linarith
  have hz : z ≠ 0 := by
    by_contra h
    have h4 : z = 0 := by linarith
    have h5 : x * y * z = 0 := by
      simp [h4, hx, hy]
    contradiction
  have h4 : 2 * x ^ 2 + 3 * y ^ 2 + 6 * z ^ 2 = 36 * z ^ 2 := by
    rw [hx, hy]
    nlinarith
  have h5 : x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 = 36 * z ^ 2 := by
    rw [hx, hy]
    nlinarith
  have h6 : 2 * x ^ 2 + 3 * y ^ 2 + 6 * z ^ 2 = x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 := by
    linarith [h4, h5]
  field_simp [show x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 ≠ 0 by
    nlinarith [sq_pos_of_ne_zero hz]
  ]
  <;> nlinarith [h6]