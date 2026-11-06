import Mathlib

theorem algebra_56749 (total_candies : ℝ) (h₀ : total_candies ≠ 0)
    (yellow_candies blue_candies red_candies : ℝ)
    (h₁ : yellow_candies = blue_candies * 1.14) (h₂ : red_candies = blue_candies * 0.86)
    (h₃ : total_candies = yellow_candies + blue_candies + red_candies) :
    yellow_candies / total_candies * 100 = 38 := by

  have eq1 : total_candies = blue_candies * 3 := by
    rw [h₃, h₁, h₂]
    ring

  have h5 : blue_candies ≠ 0 := by
    by_contra h
    have h6 : blue_candies = 0 := by
      linarith
    have h7 : total_candies = 0 := by
      rw [eq1]
      rw [h6]
      norm_num
    contradiction
  
  rw [h₁, eq1]
  field_simp [h5]
  ring_nf