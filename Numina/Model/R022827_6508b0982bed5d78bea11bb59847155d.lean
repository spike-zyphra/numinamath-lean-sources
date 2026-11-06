import Mathlib

theorem algebra_130463 (x : ℤ) :
    x = abs (2 * x - abs (60 - 2 * x)) ↔ x = 12 ∨ x = 20 ∨ x = 60 := by
  constructor
  · -- Assume x = abs (2 * x - abs (60 - 2 * x)), prove x = 12 ∨ x = 20 ∨ x = 60
    intro h
    by_cases h1 : 60 - 2 * x ≥ 0
    · -- If 60 - 2x ≥ 0, then |60 - 2x| = 60 - 2x
      have h2 : abs (60 - 2 * x) = 60 - 2 * x := by
        rw [abs_of_nonneg h1]
      rw [h2] at h
      by_cases h3 : 2 * x - (60 - 2 * x) ≥ 0
      · -- If 2x - (60 - 2x) ≥ 0, then |2x - (60 - 2x)| = 2x - (60 - 2x)
        have h4 : abs (2 * x - (60 - 2 * x)) = 2 * x - (60 - 2 * x) := by
          rw [abs_of_nonneg h3]
        rw [h4] at h
        have hx : x = 20 := by
          omega
        right
        left
        exact hx
      · -- If 2x - (60 - 2x) < 0, then |2x - (60 - 2x)| = -(2x - (60 - 2x))
        have h4 : abs (2 * x - (60 - 2 * x)) = -(2 * x - (60 - 2 * x)) := by
          rw [abs_of_neg (show 2 * x - (60 - 2 * x) < 0 by linarith)]
        rw [h4] at h
        have hx : x = 12 := by
          omega
        left
        exact hx
    · -- If 60 - 2x < 0, then |60 - 2x| = 2x - 60
      have h2 : abs (60 - 2 * x) = 2 * x - 60 := by
        rw [abs_of_neg (show 60 - 2 * x < 0 by linarith)]
        all_goals omega
      rw [h2] at h
      by_cases h3 : 2 * x - (2 * x - 60) ≥ 0
      · -- If 2x - (2x -60) ≥ 0, then |2x - (2x -60)| = 2x - (2x -60)
        have h4 : abs (2 * x - (2 * x - 60)) = 2 * x - (2 * x - 60) := by
          rw [abs_of_nonneg h3]
        rw [h4] at h
        have hx : x = 60 := by
          omega
        right
        right
        exact hx
      · -- If 2x - (2x -60) < 0, then |2x - (2x -60)| = -(2x - (2x -60))
        have h4 : abs (2 * x - (2 * x - 60)) = -(2 * x - (2 * x - 60)) := by
          rw [abs_of_neg (show 2 * x - (2 * x - 60) < 0 by linarith)]
        rw [h4] at h
        omega
  · -- Assume x = 12 ∨ x = 20 ∨ x = 60, prove x = abs (2 * x - abs (60 - 2 * x))
    rintro (h | h | h)
    · -- Case x = 12
      rw [h]
      all_goals norm_num [abs]
    · -- Case x = 20
      rw [h]
      all_goals norm_num [abs]
    · -- Case x = 60
      rw [h]
      all_goals norm_num [abs]