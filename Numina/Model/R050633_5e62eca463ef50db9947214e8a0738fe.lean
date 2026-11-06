import Mathlib

theorem algebra_102355 {x : ℝ} (hx : x > 0) (h : (1 + 120 / x) * x = (1 + 100 / (x - 120)) * (x - 120)) :
    x = 500 := by
  have h1 : (1 + 120 / x) * x = x + 120 := by
    field_simp at h ⊢
    <;> linarith
  have h2 : (1 + 100 / (x - 120)) * (x - 120) = (x - 120) + 100 := by 
    have h3 : x - 120 ≠ 0 := by 
      by_contra h_eq
      have h2 : x = 120 := by linarith
      rw [h2] at h 
      norm_num at h 
      all_goals nlinarith [hx]
    field_simp [h3] 
    <;> linarith 
  rw [h1, h2] at h 
  linarith