import Mathlib

theorem algebra_10230 : {y : ℝ | abs (y - 6) + 2 * y = 9} = {3} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume abs (y - 6) + 2 * y = 9, prove y = 3
    intro h
    by_cases h1 : y - 6 ≥ 0
    · -- y - 6 ≥ 0, so |y - 6| = y - 6
      have h2 : abs (y - 6) = y - 6 := by
        rw [abs_of_nonneg]
        linarith
      rw [h2] at h
      linarith
    · -- y - 6 < 0, so |y - 6| = 6 - y
      have h2 : abs (y - 6) = 6 - y := by
        rw [abs_of_neg (show y - 6 < 0 by linarith)]
        ring
      rw [h2] at h
      linarith
  · -- Assume y = 3, prove abs (y - 6) + 2 * y = 9
    intro h
    rw [h]
    norm_num [abs_of_neg]
    all_goals norm_num