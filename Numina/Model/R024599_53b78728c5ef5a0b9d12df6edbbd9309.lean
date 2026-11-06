import Mathlib

theorem inequalities_5768
    (x y : ℝ) :
    1 + |x * y - 1| ≤ (1 + |x - 1|) * (1 + |y - 1|) := by
  by_cases h1 : x - 1 ≥ 0
  · -- Case x ≥ 1
    have hx1 : |x - 1| = x - 1 := by
      rw [abs_of_nonneg h1]
    by_cases h2 : y - 1 ≥ 0
    · -- Case y ≥ 1
      have hy1 : |y - 1| = y - 1 := by
        rw [abs_of_nonneg h2]
      have h3 : x * y - 1 ≥ 0 := by
        nlinarith [show x ≥ 1 by linarith, show y ≥ 1 by linarith]
      have hxy : |x * y - 1| = x * y - 1 := by
        rw [abs_of_nonneg h3]
      rw [hxy, hx1, hy1]
      nlinarith
    · -- Case y < 1
      have hy1 : |y - 1| = 1 - y := by
        rw [abs_of_neg (by linarith)]
        all_goals linarith
      by_cases h3 : x * y - 1 ≥ 0
      · -- Case x * y ≥ 1
        have hxy1 : |x * y - 1| = x * y - 1 := by
          rw [abs_of_nonneg h3]
        rw [hxy1, hx1, hy1]
        nlinarith
      · -- Case x * y < 1
        have h3' : x * y - 1 < 0 := by linarith
        have hxy1 : |x * y - 1| = 1 - x * y := by
          rw [abs_of_neg h3']
          all_goals linarith
        rw [hxy1, hx1, hy1]
        nlinarith
  · -- Case x < 1
    have hx1 : |x - 1| = 1 - x := by
      rw [abs_of_neg (by linarith)]
      all_goals linarith
    by_cases h2 : y - 1 ≥ 0
    · -- Case y ≥ 1
      have hy1 : |y - 1| = y - 1 := by
        rw [abs_of_nonneg h2]
      by_cases h3 : x * y - 1 ≥ 0
      · -- Case x * y ≥ 1
        have hxy1 : |x * y - 1| = x * y - 1 := by
          rw [abs_of_nonneg h3]
        rw [hxy1, hx1, hy1]
        nlinarith
      · -- Case x * y < 1
        have h3' : x * y - 1 < 0 := by linarith
        have hxy1 : |x * y - 1| = 1 - x * y := by
          rw [abs_of_neg h3']
          all_goals linarith
        rw [hxy1, hx1, hy1]
        nlinarith
    · -- Case y < 1
      have hy1 : |y - 1| = 1 - y := by
        rw [abs_of_neg (by linarith)]
        all_goals linarith
      by_cases h3 : x * y - 1 ≥ 0
      · -- Case x * y ≥ 1
        have hxy1 : |x * y - 1| = x * y - 1 := by
          rw [abs_of_nonneg h3]
        rw [hxy1, hx1, hy1]
        nlinarith
      · -- Case x * y < 1
        have h3' : x * y - 1 < 0 := by linarith
        have hxy1 : |x * y - 1| = 1 - x * y := by
          rw [abs_of_neg h3']
          all_goals linarith
        rw [hxy1, hx1, hy1]
        nlinarith