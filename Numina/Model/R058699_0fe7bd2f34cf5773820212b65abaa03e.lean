import Mathlib

theorem algebra_238370 {f : ℝ → ℝ} (hodd : ∀ x, f (-x + 1) = -f (x + 1)) (heven : ∀ x, f (-x - 1) = f (x - 1)) (hf0 : f 0 = 2) : f 4 = -2 := by
  have h2 : f 2 = -2 := by
    specialize hodd 1
    norm_num at hodd
    linarith [hf0, hodd]
  have h3 : f (-4 : ℝ) = -2 := by
    have h4 : f (-4 : ℝ) = f (2 : ℝ) := by
      specialize heven 3
      norm_num at heven
      linarith [heven, h2]
    rw [h4, h2]
    all_goals norm_num
  have h5 : f (-2 : ℝ) = -f 4 := by
    specialize hodd 3
    norm_num at hodd
    linarith [hodd]
  have h6 : f (-2 : ℝ) = 2 := by
    specialize heven 1
    norm_num at heven
    linarith [hf0, heven]
  linarith [h5, h6]