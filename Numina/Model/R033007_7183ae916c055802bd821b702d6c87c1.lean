import Mathlib

open Real

theorem algebra_297847 {f : ℕ → ℝ} (hf : ∀ n, f n = (4 * (1 - (1 / 4) ^ n) + 2 * (1 / 4) ^ n) / 6)
    (h : f n > 0.9999) :
    IsLeast {n | f n > 0.9999} 9 := by
  have h1 : f n ≤ (2 / 3 : ℝ) := by
    rw [hf n]
    have h2 : (1 / 4 : ℝ) ^ n ≥ 0 := by positivity
    linarith
  have h2 : (2 / 3 : ℝ) < (0.9999 : ℝ) := by norm_num
  linarith