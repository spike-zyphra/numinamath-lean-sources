import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_320450 {t : ℝ} (a b : ℕ → ℝ)
  (ha : ∀ n, a n = n ^ 3 - n ^ 2 - 2 * t * n + t ^ 2)
  (hb : ∀ n, b n = n ^ 3 - 2 * n ^ 2 - n + 5 / 4)
  (h : ∀ n, 0 < n → a n ≥ b n) :
  t ≤ 1 / 2 ∨ t ≥ 3 / 2 := by
  have h1 := h 1 (by norm_num)
  rw [ha, hb] at h1
  norm_num at h1
  have h2 : (t - 1) ^ 2 ≥ 1 / 4 := by 
    nlinarith 
  by_cases h3 : t - 1 ≤ -1 / 2
  · left
    linarith 
  · right
    have h4 : t - 1 ≥ 1 / 2 := by nlinarith 
    linarith