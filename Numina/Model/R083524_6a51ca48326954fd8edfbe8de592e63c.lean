import Mathlib

theorem algebra_10689 (x : ℝ) : ¬(0 < abs (3 * x + 5)) ↔ x = -5 / 3 := by
  constructor
  · -- Assume ¬(0 < abs (3 * x + 5)), prove x = -5 / 3
    intro h
    have h1 : abs (3 * x + 5) ≤ 0 := by
      by_contra h2
      push_neg at h2
      have h2' : 0 < abs (3 * x + 5) := by linarith
      contradiction
    have h2 : abs (3 * x + 5) = 0 := by
      linarith [abs_nonneg (3 * x + 5), h1]
    have h3 : 3 * x + 5 = 0 := by
      rwa [abs_eq_zero] at h2
    linarith
  · -- Assume x = -5 / 3, prove ¬(0 < abs (3 * x + 5))
    intro h
    rw [h]
    norm_num [abs_zero]
    all_goals norm_num [abs_nonneg]