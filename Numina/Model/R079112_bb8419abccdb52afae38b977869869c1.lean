import Mathlib

theorem other_261742 (n : ℕ) (h₀ : n = 99 + 72) (h₁ : (99 * 122 + 72 * 163) / n = 155 * (n - 72) / 99 + 148 * (n - 99) / 72) :
    n = 621 := by
  norm_num [show n = 99 + 72 by linarith [h₀]] at h₁
  all_goals omega