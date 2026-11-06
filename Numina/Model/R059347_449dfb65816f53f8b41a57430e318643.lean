import Mathlib

theorem algebra_7983
    (a b : ℝ)
    (M N : ℝ)
    (hM : M = 10 * a ^ 2 + a + b ^ 2 - 2 * b + 9)
    (hN : N = a ^ 2 + 25 * a + (b - 1) ^ 2 - 9) :
    M - N > 0 := by
  have h1 : M - N = 9 * a^2 - 24 * a + 17 := by
    rw [hM, hN]
    ring_nf
  rw [h1]
  have h2 : 9 * a^2 - 24 * a + 17 > 0 := by
    nlinarith [sq_nonneg (a - 4 / 3)]
  linarith