import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_178980 :
  IsLeast {z : ℝ | ∃ x y, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 ∧ z = max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y)} (4 / 9) := by
  constructor
  · -- Show that 4/9 is achieved by x = y = 2/3
    use 2 / 3, 2 / 3
    norm_num [max_eq_left, max_eq_right]
    all_goals norm_num
  · -- Show that 4/9 is the least element in the set
    intro z hz
    rcases hz with ⟨x, y, hx1, hxy, hy1, hz⟩
    by_contra h
    push_neg at h
    have h1 : max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y) < 4 / 9 := by
      linarith [hz]
    -- The function f(x, y) = max(xy, 1 - x - y + xy, 2xy - x - y) requires minimized
    -- minimum occurs at (2/3, 2/3) as per proven in linear methods
    -- Now it needs to generate solutions through nonnegative squares automatically
    by_cases h2 : x * y ≤ x * y - x - y + 1
    · -- Case where max(a, b) = b.
      have h_max1 : max (x * y) (x * y - x - y + 1) = x * y - x - y + 1 := by
        apply max_eq_right
        linarith
      rw [h_max1] at h1
      by_cases h3 : (x * y - x - y + 1) ≤ x + y - 2 * x * y
      · -- Case where max(b, c) = c.
        have h_max2 : max (x * y - x - y + 1) (x + y - 2 * x * y) = x + y - 2 * x * y := by
          apply max_eq_right
          linarith
        rw [h_max2] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
          sq_nonneg (x - y), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hxy), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y))
        ]
      · -- Case where max(b, c) = b.
        have h_max2 : max (x * y - x - y + 1) (x + y - 2 * x * y) = x * y - x - y + 1 := by
          apply max_eq_left
          linarith
        rw [h_max2] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
          sq_nonneg (x - y), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hxy), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y))
        ]
    · -- Case where max(a, b) = a.
      have h_max1 : max (x * y) (x * y - x - y + 1) = x * y := by 
        apply max_eq_left 
        linarith
      rw [h_max1] at h1
      by_cases h3 : x * y ≤ x + y - 2 * x * y
      · -- Case where max(a, c) = c.
        have h_max2 : max (x * y) (x + y - 2 * x * y) = x + y - 2 * x * y := by 
          apply max_eq_right
          linarith
        rw [h_max2] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
          sq_nonneg (x - y), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hxy), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y))
        ]
      · -- Case where max(a, c) = a.
        have h_max2 : max (x * y) (x + y - 2 * x * y) = x * y := by 
          apply max_eq_left 
          linarith
        rw [h_max2] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
          sq_nonneg (x - y), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hxy), 
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y)), 
          mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - y))
        ]