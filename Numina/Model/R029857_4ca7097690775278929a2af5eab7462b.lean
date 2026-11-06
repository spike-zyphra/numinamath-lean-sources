import Mathlib

theorem algebra_20875 {x y : ℝ} (h₀ : x + y = 15) (h₁ : 4 * min x y = 2 * max x y - 60) :
    max x y = 20 := by
  by_cases h2 : x ≤ y
  · -- If x ≤ y, then min x y = x and max x y = y
    have h3 : min x y = x := by
      apply min_eq_left
      linarith
    have h4 : max x y = y := by
      apply max_eq_right
      linarith
    rw [h3, h4] at h₁
    have h5 : x = -5 := by
      nlinarith
    have h6 : y = 20 := by
      linarith [h₀, h5]
    rw [h4]
    linarith [h6]
  · -- If y < x, then min x y = y and max x y = x
    have h3 : min x y = y := by
      apply min_eq_right
      linarith
    have h4 : max x y = x := by
      apply max_eq_left
      linarith
    rw [h3, h4] at h₁
    have h5 : y = -5 := by
      nlinarith
    have h6 : x = 20 := by
      linarith [h₀, h5]
    rw [h4]
    linarith [h6]