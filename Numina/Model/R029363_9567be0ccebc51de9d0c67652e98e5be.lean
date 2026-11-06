import Mathlib

theorem algebra_181080 :
    {(x, y) : ℝ × ℝ | 2 * x - 3 * abs y = 1 ∧ abs x + 2 * y = 4 } = {(2, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfy both equations, prove (x, y) = (2, 1)
    rintro ⟨h1, h2⟩
    by_cases h3 : y ≥ 0
    · -- If y ≥ 0, then |y| = y
      have h4 : abs y = y := abs_of_nonneg h3
      rw [h4] at h1
      by_cases h5 : x ≥ 0
      · -- If x ≥ 0, then |x| = x
        have h6 : abs x = x := abs_of_nonneg h5
        rw [h6] at h2
        have hx : x = 2 := by
          linarith
        have hy : y = 1 := by
          linarith
        simp [hx, hy]
      · -- If x < 0, then |x| = -x
        have h6 : abs x = -x := abs_of_neg (lt_of_not_ge h5)
        rw [h6] at h2
        linarith
    · -- If y < 0, then |y| = -y
      have h4 : abs y = -y := abs_of_neg (lt_of_not_ge h3)
      rw [h4] at h1
      by_cases h5 : x ≥ 0
      · -- If x ≥ 0, then |x| = x
        have h6 : abs x = x := abs_of_nonneg h5
        rw [h6] at h2
        linarith
      · -- If x < 0, then |x| = -x
        have h6 : abs x = -x := abs_of_neg (lt_of_not_ge h5)
        rw [h6] at h2
        linarith
  · -- Show that (2, 1) satisfies both equations
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Check first equation
      norm_num [abs_of_nonneg]
    · -- Check second equation
      norm_num [abs_of_nonneg]