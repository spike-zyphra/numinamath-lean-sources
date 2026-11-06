import Mathlib

theorem algebra_286901 {x y z : ℝ} (h1 : x - y = 2) (h2 : x * y + z ^ 2 = -1) :
    x = 1 ∧ y = -1 ∧ z = 0 := by 
  have h3 : x = y + 2 := by linarith [h1]

  rw [h3] at h2
  
  have h4 : (y + 1)^2 + z^2 = 0 := by 
    nlinarith
  
  have h5 : (y + 1)^2 = 0 := by 
    linarith [sq_nonneg (y + 1), sq_nonneg z]
  
  have h6 : z^2 = 0 := by 
    linarith [sq_nonneg (y + 1), sq_nonneg z]

  have hy : y = -1 := by
    have h7 : y + 1 = 0 := by 
      rwa [sq_eq_zero_iff] at h5
    linarith
  
  have hz : z = 0 := by 
    rwa [sq_eq_zero_iff] at h6

  have hx : x = 1 := by 
    rw [hy] at h3
    linarith
  
  exact ⟨hx, hy, hz⟩