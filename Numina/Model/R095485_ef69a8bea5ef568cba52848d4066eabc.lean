import Mathlib

theorem algebra_193355 {x y z : ℝ} (h1 : x = 80 / 100 * y) (h2 : y * 9 / 20 = z * 0.5) (h3 : x + z = y + 70) :
    x = 80 ∧ y = 100 ∧ z = 90 := by
  have h4 : y = 100 := by
    nlinarith [sq_nonneg (x - 80), sq_nonneg (y - 100), sq_nonneg (z - 90)]
  have hx : x = 80 := by
    rw [h4] at h1
    nlinarith
  have h5 : z = 90 := by
    rw [hx, h4] at h3
    nlinarith
  exact ⟨hx, h4, h5⟩