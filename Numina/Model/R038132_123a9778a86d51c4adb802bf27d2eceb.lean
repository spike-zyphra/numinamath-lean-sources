import Mathlib

open Real

theorem inequalities_328052 (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (h : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a + b + c = 1 → u * (a * b + b * c + c * a) +
      v * a * b * c ≤ 7 / 3) :
    u * v ≤ 441 / 4 := by
  have h1 := h (1 / 3) (1 / 3) (1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1
  have h2 := h (1 / 2) (1 / 3) (1 / 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h2
  have h3 := h (1 / 2) (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h3
  have h4 := h (2 / 5) (2 / 5) (1 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h4
  nlinarith [sq_nonneg (u - 7 / 2), sq_nonneg (v - 63 / 2), mul_pos hu hv]