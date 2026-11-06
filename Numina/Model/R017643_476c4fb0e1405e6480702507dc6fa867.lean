import Mathlib

theorem algebra_287570 {x y : ℝ} (h₀ : abs x + x + 5 * y = 2) (h₁ : abs y - y + x = 7) : x + y = 3 := by
  by_cases hx : x ≥ 0
  · -- If x ≥ 0, then |x| = x
    have h2 : abs x = x := by
      rw [abs_of_nonneg hx]
    rw [h2] at h₀
    by_cases hy : y ≥ 0
    · -- If y ≥ 0, then |y| = y
      have h3 : abs y = y := by 
        rw [abs_of_nonneg hy]
      rw [h3] at h₁
      nlinarith
    · -- If y < 0, then |y| = -y
      have h4 : abs y = -y := by
        rw [abs_of_neg (show y < 0 by linarith)]
      rw [h4] at h₁
      linarith
  · -- If x < 0, then |x| = -x
    have h5 : abs x = -x := by
      rw [abs_of_neg (show x < 0 by linarith)]
    rw [h5] at h₀
    by_cases hy : y ≥ 0
    · -- If y ≥ 0, then |y| = y
      have h6 : abs y = y := by 
        rw [abs_of_nonneg hy]
      rw [h6] at h₁
      nlinarith
    · -- If y < 0, then |y| = -y
      have h7 : abs y = -y := by 
        rw [abs_of_neg (show y < 0 by linarith)]
      rw [h7] at h₁
      linarith