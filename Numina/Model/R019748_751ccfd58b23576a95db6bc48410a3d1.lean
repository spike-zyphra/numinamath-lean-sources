import Mathlib

theorem algebra_159792 {x y z : ℝ} (h₀ : x + y + z = 2) (h₁ : 1 / x + 1 / y + 1 / z = 0) :
    x ^ 2 + y ^ 2 + z ^ 2 = 4 := by
  have hx : x ≠ 0 := by 
    by_contra h
    have h_eq : x = 0 := by linarith
    rw [h_eq] at h₀ h₁
    have : y + z = 2 := by linarith
    field_simp [(show y ≠ 0 from by 
      by_contra h'
      rw [h'] at h₁
      norm_num at h₁ 
      all_goals nlinarith
    ), (show z ≠ 0 from by 
      by_contra h'
      rw [h'] at h₁
      norm_num at h₁ 
      all_goals nlinarith
    )] at h₁
    all_goals nlinarith
  have hy : y ≠ 0 := by 
    by_contra h
    have h_eq : y = 0 := by linarith
    rw [h_eq] at h₀ h₁
    have : x + z = 2 := by linarith
    field_simp [(show x ≠ 0 from by 
      by_contra h'
      rw [h'] at h₁
      norm_num at h₁ 
      all_goals nlinarith
    ), (show z ≠ 0 from by 
      by_contra h'
      rw [h'] at h₁
      norm_num at h₁ 
      all_goals nlinarith
    )] at h₁
    all_goals nlinarith
  have hz : z ≠ 0 := by 
    by_contra h
    have h_eq : z = 0 := by linarith
    rw [h_eq] at h₀ h₁
    have : x + y = 2 := by linarith
    field_simp [(show x ≠ 0 from by 
      by_contra h'
      rw [h'] at h₁
      norm_num at h₁ 
      all_goals nlinarith
    ), (show y ≠ 0 from by 
      by_contra h'
      rw [h'] at h₁
      norm_num at h₁ 
      all_goals nlinarith
    )] at h₁
    all_goals nlinarith
  have h2 : x * y + y * z + z * x = 0 := by 
    field_simp [hx, hy, hz] at h₁ 
    linarith 
  have h3 : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z)^2 - 2 * (x * y + y * z + z * x) := by 
    ring 
  rw [h3, h₀, h2] 
  all_goals norm_num 
  all_goals linarith