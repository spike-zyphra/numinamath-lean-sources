import Mathlib

theorem algebra_199099 (x y : ℝ) (h₀ : abs x + x + y = 10) (h₁ : abs y + x - y = 10)
    (P : ℝ) (hP : P = x + y) : P = 4 := by
  by_cases hx : x ≥ 0
  · -- Case 1: $x \geq 0$
    rw [abs_of_nonneg hx] at h₀
    by_cases hy : y ≥ 0
    · -- Subcase 1.1: $y \geq 0$
      rw [abs_of_nonneg hy] at h₁
      have h2 : x = 10 := by linarith
      rw [h2] at h₀
      have h3 : y = 0 := by linarith
      rw [hP, h2, h3]
      linarith
    · -- Subcase 1.2: $y < 0$
      rw [abs_of_neg (lt_of_not_ge hy)] at h₁
      have h2 : 2 * x + y = 10 := by linarith
      have h3 : x - 2 * y = 10 := by linarith
      have hx' : x = 6 := by
        linarith
      have hy' : y = -2 := by
        rw [hx'] at h2
        linarith
      have hP' : P = 4 := by
        rw [hP, hx', hy']
        linarith
      exact hP'
  · -- Case 2: $x < 0$
    rw [abs_of_neg (lt_of_not_ge hx)] at h₀
    by_cases hy : y ≥ 0
    · -- Subcase 2.1: $y \geq 0$
      rw [abs_of_nonneg hy] at h₁
      have h2 : y = 10 := by linarith
      rw [h2] at h₀
      have h3 : x = 0 := by linarith
      linarith
    · -- Subcase 2.2: $y < 0$
      rw [abs_of_neg (lt_of_not_ge hy)] at h₁
      have h2 : y = 10 := by linarith
      linarith