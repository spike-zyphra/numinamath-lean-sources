import Mathlib

theorem algebra_1197
    {x y : ℝ} (h₁ : 2 * x - abs y = - 7) (h₂ : 3 * abs x + 2 * y = 0) :
    x * y = 6 := by
  by_cases h3 : x ≥ 0
  · -- Assume x ≥ 0, so |x| = x
    have h4 : abs x = x := abs_of_nonneg h3
    rw [h4] at h₂
    by_cases h5 : y ≥ 0
    · -- Assume y ≥ 0, so |y| = y
      have h6 : abs y = y := abs_of_nonneg h5
      rw [h6] at h₁
      nlinarith
    · -- Assume y < 0, so |y| = -y
      have h7 : abs y = -y := abs_of_neg (show y < 0 by linarith)
      rw [h7] at h₁
      nlinarith
  · -- Assume x < 0, so |x| = -x
    have h8 : abs x = -x := abs_of_neg (show x < 0 by linarith)
    rw [h8] at h₂
    by_cases h9 : y ≥ 0
    · -- Assume y ≥ 0, so |y| = y
      have h10 : abs y = y := abs_of_nonneg h9
      rw [h10] at h₁
      nlinarith
    · -- Assume y < 0, so |y| = -y
      have h11 : abs y = -y := abs_of_neg (show y < 0 by linarith)
      rw [h11] at h₁
      have hx : x = -2 := by linarith
      have hy : y = -3 := by linarith
      rw [hx, hy]
      norm_num