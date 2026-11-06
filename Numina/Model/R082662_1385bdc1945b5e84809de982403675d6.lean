import Mathlib

theorem algebra_12101 {x y : ℝ} (h₀ : x + y = 30) (h₁ : 2 * max x y - 3 * min x y = 5) :
    abs (max x y - min x y) = 8 := by
  by_cases h2 : x ≥ y
  · -- Case where x ≥ y: max x y = x, min x y = y
    have h3 : max x y = x := by
      apply max_eq_left
      linarith
    have h4 : min x y = y := by
      apply min_eq_right
      linarith
    rw [h3, h4] at h₁
    have hx1 : x = 19 := by 
      linarith
    have hy1 : y = 11 := by 
      linarith [h₀, hx1]
    rw [h3, h4]
    rw [hx1, hy1]
    norm_num [abs]
    <;> nlinarith
  · -- Case where y > x: max x y = y, min x y = x
    have h5 : max x y = y := by
      apply max_eq_right
      linarith
    have h6 : min x y = x := by
      apply min_eq_left
      linarith
    rw [h5, h6] at h₁
    have hy2 : y = 19 := by 
      linarith
    have hx2 : x = 11 := by 
      linarith [h₀, hy2]
    rw [h5, h6]
    rw [hx2, hy2]
    norm_num [abs]
    <;> nlinarith
  all_goals linarith
  all_goals norm_num [abs]
  <;> nlinarith