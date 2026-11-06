import Mathlib

theorem algebra_20644 {x y z w : ℝ} (h₀ : x / y = 4 / 5) (h₁ : y / z = 3 / 10)
    (h₂ : z / w = 6 / 7) : (x + y + w) / z = 128 / 75 := by

  have hy : y ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
  
  have hz : z ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  
  have hw : w ≠ 0 := by
    by_contra h
    rw [h] at h₂
    norm_num at h₂
  
  have eq1 : y = 3 / 10 * z := by 
    field_simp [hz] at h₁
    linarith
  
  have eq2 : x = 4 / 5 * y := by 
    field_simp [hy] at h₀
    linarith
  
  have eq3 : x = 6 / 25 * z := by 
    rw [eq2, eq1]
    ring
  
  have eq4 : w = 7 / 6 * z := by 
    field_simp [hw] at h₂
    linarith
  
  have eq5 : x + y + w = 128 / 75 * z := by 
    rw [eq3, eq1, eq4]
    ring
  
  field_simp [hz]
  linarith [eq5]