import Mathlib

theorem algebra_243169 {a b : ℝ} (h1 : 3 * a - 2 * abs b = 5) (h2 : 4 * abs a - 6 * a = 3 * b) :
    a ^ 2 + b ^ 2 = 13 := by

  by_cases hbx : b ≥ 0
  · -- Case where b ≥ 0, so abs b = b.
    rw [abs_of_nonneg hbx] at h1
    by_cases hax : a ≥ 0
    · -- Case where a ≥ 0, so abs a = a.
      rw [abs_of_nonneg hax] at h2
      nlinarith
    · -- Case where a < 0, so abs a = -a.
      rw [abs_of_neg (show a < 0 by linarith)] at h2
      nlinarith
  · -- Case where b < 0, so abs b = -b.
    rw [abs_of_neg (show b < 0 by linarith)] at h1
    by_cases hax : a ≥ 0
    · -- Case where a ≥ 0, so abs a = a.
      rw [abs_of_nonneg hax] at h2
      nlinarith
    · -- Case where a < 0, so abs a = -a.
      rw [abs_of_neg (show a < 0 by linarith)] at h2
      nlinarith