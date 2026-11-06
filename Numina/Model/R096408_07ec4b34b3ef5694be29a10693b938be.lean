import Mathlib

theorem inequalities_224216 (a : ℝ) : abs (-a) > -a ↔ a > 0 := by
  constructor
  · -- Assume abs (-a) > -a, we need to prove a > 0
    intro h
    by_cases h1 : -a ≥ 0
    · -- Case -a ≥ 0, i.e., a ≤ 0
      rw [abs_of_nonneg h1] at h
      linarith
    · -- Case -a < 0, i.e., a > 0
      push_neg at h1
      rw [abs_of_neg h1] at h
      linarith
  · -- Assume a > 0, we need to prove abs (-a) > -a
    intro h
    have h1 : -a < 0 := by linarith
    rw [abs_of_neg h1]
    linarith