import Mathlib

theorem inequalities_129190 (a : ℕ → ℝ) (h : ∀ n k, 1 ≤ n → n ≤ 2022 → 1 ≤ k → k ≤ 2022 → a n - a k ≥ n ^ 3 - k ^ 3)
    (ha : a 1011 = 0) :
    a 2022 = 2022 ^ 3 - 1011 ^ 3 := by
  have h1 := h 2022 1011 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := h 1011 2022 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [ha] at h1 h2 ⊢
  linarith