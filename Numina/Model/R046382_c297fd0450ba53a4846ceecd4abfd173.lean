import Mathlib

theorem algebra_199099 (x y : ℝ) (h₀ : abs x + x + y = 10) (h₁ : abs y + x - y = 10)
    (P : ℝ) (hP : P = x + y) : P = 4 := by

  by_cases h2 : x ≥ 0
  · -- case x ≥ 0, so |x| = x
    rw [abs_of_nonneg h2] at h₀
    by_cases h3 : y ≥ 0
    · -- case y ≥ 0, so |y| = y
      rw [abs_of_nonneg h3] at h₁
      nlinarith [hP]
    · -- case y < 0, so |y| = -y
      rw [abs_of_neg (not_le.mp h3) ] at h₁
      rw [hP]
      linarith
  · -- case x < 0, so |x| = -x
    rw [abs_of_neg (not_le.mp h2) ] at h₀
    by_cases h3 : y ≥ 0
    · -- case y ≥ 0, so |y| = y
      rw [abs_of_nonneg h3] at h₁
      nlinarith [hP]
    · -- case y < 0, so |y| = -y
      rw [abs_of_neg (not_le.mp h3) ] at h₁
      nlinarith [hP]