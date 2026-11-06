import Mathlib

theorem algebra_243473 {x y : ℝ}
    (h1 : 3 * x ^ 2 + 4 * x * y + 12 * y ^ 2 + 16 * y = -6)
    (h2 : x ^ 2 - 12 * x * y + 4 * y ^ 2 - 10 * x + 12 * y = -7) :
    x = 1 / 2 ∧ y = -3 / 4 := by
  have h3 : 3 * x ^ 2 - 36 * x * y + 12 * y ^ 2 - 30 * x + 36 * y = -21 := by
    nlinarith [h2]
  have h4 : -40 * x * y - 30 * x + 20 * y = -15 := by
    nlinarith [h1, h3]
  have h5 : 8 * x * y + 6 * x - 4 * y = 3 := by
    nlinarith
  have h6 : (4 * y + 3) * (2 * x - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case where 4 * y + 3 = 0, so y = -3 / 4
    have hy : y = -3 / 4 := by linarith
    have hx : x = 1 / 2 := by
      rw [hy] at h1
      nlinarith
    exact ⟨hx, hy⟩
  · -- Case where 2 * x - 1 = 0, so x = 1 / 2
    have hx : x = 1 / 2 := by linarith
    have hy : y = -3 / 4 := by
      rw [hx] at h1
      nlinarith
    exact ⟨hx, hy⟩