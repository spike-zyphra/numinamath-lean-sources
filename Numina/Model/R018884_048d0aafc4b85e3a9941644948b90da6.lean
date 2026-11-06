import Mathlib

theorem algebra_96396 {p : ℝ} (x y : ℝ)
    (hx : x = 1 + 2 ^ p) (hy : y = 1 + 2 ^ (-p)) :
    y = x / (x - 1) := by

  have h1 : (2 : ℝ) ^ (-p : ℝ) = 1 / ((2 : ℝ) ^ (p : ℝ)) := by 
    field_simp [Real.rpow_neg]

  have h2 : 2 ^ p = x - 1 := by
    linarith [hx]

  have h3 : (2 : ℝ) ^ (-p : ℝ) = 1 / (x - 1) := by
    rw [h1]
    rw [h2]

  have h4 : y = 1 + (1 / (x - 1)) := by 
    rw [hy]
    rw [h3]

  have h5 : x - 1 ≠ 0 := by 
    by_contra h
    have h6 : x = 1 := by linarith 
    have h7 : (2 : ℝ) ^ p = (0 : ℝ) := by
      have h8 : x - 1 = (0 : ℝ) := by linarith 
      have h9 : (2 : ℝ) ^ p = x - 1 := by
        linarith [hx]
      rw [h8] at h9 
      linarith
    have h8 : (2 : ℝ) ^ p > (0 : ℝ) := by 
      positivity 
    linarith

  have h6 : y = x / (x - 1) := by 
    rw [h4]
    field_simp [h5]
    <;> nlinarith 

  exact h6