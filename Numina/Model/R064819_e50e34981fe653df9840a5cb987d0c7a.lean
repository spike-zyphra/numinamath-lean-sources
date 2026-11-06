import Mathlib

theorem algebra_94589 {x y : ℝ} (hx : x ≠ 0) (h1 : x / 2 = y ^ 2) (h2 : x / 4 = 4 * y) : x = 128 := by
  have eq1 : x = 16 * y := by
    linarith
  have eq2 : y = x / 16 := by
    linarith [eq1]
  rw [eq2] at h1
  have h3 : x * (x - 128) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case x = 0, contradicts hx.
    contradiction
  · -- Case x - 128 = 0, so x = 128.
    linarith