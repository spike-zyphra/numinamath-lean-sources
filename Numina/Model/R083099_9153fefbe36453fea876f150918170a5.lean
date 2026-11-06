import Mathlib

theorem algebra_2155 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x * (1 - 25 / 100)) * (y * (1 - 25 / 100))^2 = (1 - z) * x * y^2) :
    z = 37 / 64 := by
  have eq1 : (x * (1 - 25 / 100 : ℝ)) * (y * (1 - 25 / 100 : ℝ))^2 = (27 / 64 : ℝ) * x * y ^ 2 := by
    ring_nf
  rw [eq1] at h
  have h1 : (27 / 64 : ℝ) * x * y ^ 2 = (1 - z) * x * y ^ 2 := h
  have h2 : (27 / 64 : ℝ) = (1 - z) := by
    apply (mul_left_inj' hx).mp
    apply (mul_left_inj' (pow_ne_zero 2 hy)).mp
    linarith
  have h3 : z = 37 / 64 := by
    linarith
  exact h3