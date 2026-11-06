import Mathlib

theorem algebra_199531 (a : ℝ) (h : ∀ x, a * x - 3 / 2 * x ^ 2 ≤ 1 / 6)
    (h' : ∀ x ∈ Set.Icc (1 / 4) (1 / 2), a * x - 3 / 2 * x ^ 2 ≥ 1 / 8) :
    a = 1 := by
  have h1 : a * (1 / 4) - 3 / 2 * (1 / 4) ^ 2 ≥ 1 / 8 := by
    apply h'
    norm_num

  have h2 : a * (1 / 2) - 3 / 2 * (1 / 2) ^ 2 ≥ 1 / 8 := by
    apply h'
    norm_num

  have h3 : a ^ 2 ≤ 1 := by
    have hmax := h (a / 3)
    nlinarith [sq_nonneg (a / 3 - 1 / 2), sq_nonneg (a - 1)]

  nlinarith