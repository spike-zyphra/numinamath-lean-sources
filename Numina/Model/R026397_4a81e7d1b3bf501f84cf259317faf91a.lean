import Mathlib

theorem algebra_222524 {x y : ℝ} (h₀ : abs x + x + y = 10) (h₁ : x + abs y - y = 12) :
    x + y = 18 / 5 := by
  by_cases hx : x ≥ 0
  · -- x ≥ 0, so |x| = x
    have h2 : abs x = x := by
      rw [abs_of_nonneg hx]
    rw [h2] at h₀
    by_cases hy : y ≥ 0
    · -- y ≥ 0, so |y| = y
      have h3 : abs y = y := by
        rw [abs_of_nonneg hy]
      rw [h3] at h₁
      nlinarith
    · -- y < 0, so |y| = -y
      have h3 : abs y = -y := by
        rw [abs_of_neg (show y < 0 by linarith)]
      rw [h3] at h₁
      have eq1 : 2 * x + y = 10 := by linarith
      have eq2 : x - 2 * y = 12 := by linarith
      have eq3 : y = -14 / 5 := by
        linarith
      have eq4 : x = 32 / 5 := by
        linarith [eq3, eq2]
      linarith [eq4, eq3]
  · -- x < 0, so |x| = -x
    have h2 : abs x = -x := by
      rw [abs_of_neg (show x < 0 by linarith)]
    rw [h2] at h₀
    by_cases hy : y ≥ 0
    · -- y ≥ 0, so |y| = y
      have h3 : abs y = y := by
        rw [abs_of_nonneg hy]
      rw [h3] at h₁
      nlinarith
    · -- y < 0, so |y| = -y
      have h3 : abs y = -y := by
        rw [abs_of_neg (show y < 0 by linarith)]
      rw [h3] at h₁
      nlinarith