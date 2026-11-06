import Mathlib

theorem algebra_238168 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (1 - x) * y = x * (2 * y)) (h2 : (1 - x) * (1.5 * y) = x * (1.2 * y)) :
    x = 16 / 100 := by
  have h3 : (1 - x) = 2 * x := by
    apply (mul_left_inj' (ne_of_gt hy)).mp
    linarith
  have hx1 : x = 1 / 3 := by
    nlinarith
  rw [hx1] at h2
  norm_num at h2 ⊢
  nlinarith