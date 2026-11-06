import Mathlib

theorem algebra_77262 {x y : ℝ} (h1 : x^2 + y^2 - 48 * x - 29 * y + 714 = 0) (h2 : 2 * x * y - 29 * x - 48 * y + 756 = 0) :
    (x, y) = (31.5, 10.5) ∨ (x, y) = (20, 22) ∨ (x, y) = (28, 7) ∨ (x, y) = (16.5, 18.5) := by

  have h3 : (x - 31.5) * (x - 20) * (x - 28) * (x - 16.5) = 0 := by
    ring_nf at h1 h2 ⊢
    nlinarith [sq_nonneg (x - y - 21), sq_nonneg (x - y + 2), sq_nonneg (x - 31.5), sq_nonneg (y - 10.5), sq_nonneg (x - 20), sq_nonneg (y - 22), sq_nonneg (x - 28), sq_nonneg (y - 7), sq_nonneg (x - 16.5), sq_nonneg (y - 18.5)]
  
  cases' (mul_eq_zero.mp h3) with h31 h32
  cases' (mul_eq_zero.mp h31) with h311 h312
  cases' (mul_eq_zero.mp h311) with h3111 h3112
  · -- Case x = 31.5
    have hx : x = 31.5 := by linarith
    have hy : y = 10.5 := by
      rw [hx] at h1
      nlinarith
    simp [hx, hy]
  · -- Case x = 20
    have hx : x = 20 := by linarith
    have hy : y = 22 := by
      rw [hx] at h1
      nlinarith
    simp [hx, hy]
  · -- Case x = 28
    have hx : x = 28 := by linarith
    have hy : y = 7 := by
      rw [hx] at h1
      nlinarith
    simp [hx, hy]
  · -- Case x = 16.5
    have hx : x = 16.5 := by linarith
    have hy : y = 18.5 := by
      rw [hx] at h1
      nlinarith
    simp [hx, hy]