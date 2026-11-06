import Mathlib

theorem inequalities_287647 (a : ℝ) :
    (∀ x : ℝ, |x + a| - |x + 1| ≤ 2 * a) ↔ a ≥ 1 / 3 := by
  constructor
  · -- Forward direction: If |x + a| - |x + 1| ≤ 2 * a for all x, then a ≥ 1/3
    intro h
    have h1 := h (-1)
    norm_num at h1
    by_cases h2 : a - 1 ≥ 0
    · -- Case where a - 1 ≥ 0 (so |a - 1| = a - 1)
      rw [abs_of_nonneg (by linarith)] at h1
      linarith
    · -- Case where a - 1 < 0 (so |a - 1| = 1 - a)
      rw [abs_of_neg (by linarith)] at h1
      linarith
  · -- Backward direction: If a ≥ 1/3, then |x + a| - |x + 1| ≤ 2 * a for all x
    intro ha x
    by_cases h1 : x + a ≥ 0
    · -- Case where x + a ≥ 0 (so |x + a| = x + a)
      rw [abs_of_nonneg h1]
      by_cases h2 : x + 1 ≥ 0
      · -- Case where x + 1 ≥ 0 (so |x + 1| = x + 1)
        rw [abs_of_nonneg h2]
        linarith
      · -- Case where x + 1 < 0 (so |x + 1| = -(x + 1))
        rw [abs_of_neg (by linarith)]
        linarith
    · -- Case where x + a < 0 (so |x + a| = -(x + a))
      rw [abs_of_neg (by linarith)]
      by_cases h2 : x + 1 ≥ 0
      · -- Case where x + 1 ≥ 0 (so |x + 1| = x + 1)
        rw [abs_of_nonneg h2]
        linarith
      · -- Case where x + 1 < 0 (so |x + 1| = -(x + 1))
        rw [abs_of_neg (by linarith)]
        linarith