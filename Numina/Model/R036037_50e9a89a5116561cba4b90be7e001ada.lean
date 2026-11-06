import Mathlib

theorem algebra_11060 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    ∃ k : ℤ, (1 / a + 1 / b + 1 / c) ^ (2 * k + 1) =
    1 / (a ^ (2 * k + 1)) + 1 / (b ^ (2 * k + 1)) + 1 / (c ^ (2 * k + 1)) ∧
    (1 / a ^ (2 * k + 1) + 1 / b ^ (2 * k + 1) + 1 / c ^ (2 * k + 1)) =
    1 / (a ^ (2 * k + 1) + b ^ (2 * k + 1) + c ^ (2 * k + 1)) := by

  use 0
  constructor
  · -- Show (1/a + 1/b + 1/c)^(2*k+1) = 1/(a^(2*k+1)) + 1/(b^(2*k+1)) + 1/(c^(2*k+1))
    norm_num
  · -- Show $\frac{1}{a^{2k+1}}+\frac{1}{b^{2k+1}}+\frac{1}{c^{2k+1}}=\frac{1}{a^{2k+1} +b^{2k+1} +c^{2k+1}}$
    have h1 : 1 / a + 1 / b + 1 / c = 1 / (a + b + c) := h
    norm_num at h1 ⊢
    all_goals linarith