import Mathlib

theorem algebra_217883 (x y : ℝ) :
    (|y - x| = 2 * (x + y) ∧ |x| + |y| = 4) ↔ (x = -1 ∧ y = 3) ∨ (x = 3 ∧ y = -1) := by
  constructor
  · -- Forward direction: if the equations hold, prove the solutions
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : y - x ≥ 0
    · -- If y - x ≥ 0, then |y - x| = y - x
      have eq1 : |y - x| = y - x := by
        rw [abs_of_nonneg h3]
      rw [eq1] at h1
      have eq2 : y = -3 * x := by linarith
      by_cases h4 : x ≥ 0
      · -- Subcase 1.1 inconsistency
        have eq3 : |x| = x := abs_of_nonneg h4
        have eq4 : |y| = 3 * x := by
          have eq5 : y = -3 * x := by linarith [eq2]
          rw [eq5]
          have : |-3 * x| = 3 * x := by
            rw [abs_of_nonpos (show -3 * x ≤ (0 : ℝ) by nlinarith)]
            all_goals linarith
          linarith [this]
        nlinarith [show y ≥ x by linarith, eq2]
      · -- Subcase 1.2 valid solution (-1,3)
        have eq3 : |x| = -x := by
          rw [abs_of_neg (show x < (0 : ℝ) by linarith)]
        have eq4 : |y| = -3 * x := by
          have eq5 : y = -3 * x := by linarith [eq2]
          rw [eq5]
          have : |-3 * x| = -3 * x := by
            rw [abs_of_pos (show -3 * x > (0 : ℝ) by nlinarith)]
            all_goals linarith
          linarith [this]
        have eq5 : |x| + |y| = 4 := h2
        rw [eq3] at eq5
        rw [eq4] at eq5
        have hx1 : x = -1 := by nlinarith
        have hy1 : y = 3 := by
          linarith [hx1, eq2]
        left
        constructor
        · exact hx1
        · exact hy1
    · -- Case y - x < 0, so |y - x| = x - y
      have eq1 : |y - x| = x - y := by
        rw [abs_of_neg (show y - x < (0 : ℝ) by linarith)]
        all_goals linarith
      rw [eq1] at h1
      have eq2 : x = -3 * y := by linarith
      by_cases h4 : y ≥ 0
      · -- Subcase 2.1 inconsistency
        have eq3 : |x| = 3 * y := by
          have eq4 : x = -3 * y := by linarith [eq2]
          rw [eq4]
          have : |-3 * y| = 3 * y := by
            rw [abs_of_nonpos (show -3 * y ≤ 0 by nlinarith)]
            all_goals nlinarith
          linarith [this]
        have eq4 : |y| = y := abs_of_nonneg h4
        have eq5 : |x| + |y| = 4 := h2
        rw [eq3] at eq5
        rw [eq4] at eq5
        nlinarith [show y < x by linarith, eq2]
      · -- Subcase 2.2 valid solution (3,-1)
        have eq3 : |x| = -3 * y := by
          have eq4 : x = -3 * y := by linarith [eq2]
          rw [eq4]
          have : |-3 * y| = -3 * y := by
            rw [abs_of_pos (show -3 * y > (0 : ℝ) by nlinarith)]
            all_goals nlinarith
          linarith [this]
        have eq4 : |y| = -y := by
          rw [abs_of_neg (show y < 0 by linarith)]
        have eq5 : |x| + |y| = 4 := h2
        rw [eq3] at eq5
        rw [eq4] at eq5
        have hy1 : y = -1 := by nlinarith
        have hx1 : x = 3 := by
          linarith [hy1, eq2]
        right
        constructor
        · exact hx1
        · exact hy1
  · -- Backward direction: the solutions satisfy the system
    rintro (h | h)
    · -- First solution (-1,3)
      rcases h with ⟨hx, hy⟩
      constructor
      · -- First equation
        rw [hx, hy]
        norm_num [abs_of_pos]
      · -- Second equation
        rw [hx, hy]
        norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Second solution (3,-1)
      rcases h with ⟨hx, hy⟩
      constructor
      · -- First equation
        rw [hx, hy]
        norm_num [abs_of_neg]
      · -- Second equation
        rw [hx, hy]
        norm_num [abs_of_nonneg, abs_of_nonpos]