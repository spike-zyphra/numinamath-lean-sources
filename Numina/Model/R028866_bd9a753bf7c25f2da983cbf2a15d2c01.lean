import Mathlib

theorem algebra_119673 {x : ℝ} (hx : x^3 + x^2 + 2 * x + 2 = 0) :
    ∑ i ∈ Finset.range 1005, x^(-2 * i : ℤ) + ∑ i ∈ Finset.range 1005, x ^ (2 * i + 1) = 0 := by
  have h1 : (x + 1) * (x ^ 2 + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h1) with h2 h3
  · -- Case x + 1 = 0, so x = -1
    have hx1 : x = -1 := by linarith
    rw [hx1]
    norm_num
  · -- Case x^2 + 2 = 0, which is impossible for real x
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2 + 2)]