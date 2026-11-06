import Mathlib

theorem algebra_249643 : {(x, y) : ℝ×ℝ | abs x + abs (y - 1) = 1 ∧ x + 2 * y = 3} = {(1, 1), (-1/3, 5/3)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume ⟨x, y⟩ is in the set, prove it's in {(1, 1), (-1/3, 5/3)}
    rintro ⟨h1, h2⟩
    by_cases h3 : x ≥ 0
    · -- x ≥ 0, so |x| = x
      rw [abs_of_nonneg h3] at h1
      by_cases h4 : y - 1 ≥ 0
      · -- y - 1 ≥ 0, so |y - 1| = y - 1
        rw [abs_of_nonneg h4] at h1
        have hy : y = 1 := by linarith
        have hx : x = 1 := by linarith
        left
        simp [hx, hy]
      · -- y - 1 < 0, so |y - 1| = 1 - y
        rw [abs_of_neg (show y - 1 < 0 by linarith)] at h1
        linarith
    · -- x < 0, so |x| = -x
      rw [abs_of_neg (show x < 0 by linarith)] at h1
      by_cases h4 : y - 1 ≥ 0
      · -- y - 1 ≥ 0, so |y - 1| = y - 1
        rw [abs_of_nonneg h4] at h1
        have hx : x = -1 / 3 := by linarith
        have hy : y = 5 / 3 := by linarith
        right
        simp [hx, hy]
      · -- y - 1 < 0, so |y - 1| = 1 - y
        rw [abs_of_neg (show y - 1 < 0 by linarith)] at h1
        linarith
  · -- Show that (1,1) and (-1/3, 5/3) satisfy the system
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (1, 1)
      constructor
      · norm_num [abs_of_nonneg]
      · norm_num
    · -- Check (-1/3, 5/3)
      constructor
      · norm_num [abs_of_nonneg, abs_of_neg]
      · norm_num