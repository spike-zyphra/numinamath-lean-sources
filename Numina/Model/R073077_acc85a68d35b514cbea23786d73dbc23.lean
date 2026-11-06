import Mathlib

theorem algebra_19807 {A B : ℝ} (hA : 2 / 5 = A / 60) (hB : 60 / B = A / 60) : A + B = 174 := by
  have h1 : A = 24 := by 
    linarith
  have h2 : B ≠ 0 := by 
    by_contra h
    rw [h] at hB
    rw [h1] at hB
    norm_num at hB 
    <;> linarith 
  have h3 : A * B = 3600 := by 
    field_simp [h2] at hB 
    linarith 
  have h4 : B = 150 := by 
    rw [h1] at h3 
    linarith 
  linarith [h1, h4]