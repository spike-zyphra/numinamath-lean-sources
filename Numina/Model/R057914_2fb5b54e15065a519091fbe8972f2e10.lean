import Mathlib

theorem algebra_131326 (x y z : ℝ)
    (h₀ : x^2 + y^2 + 4 * z^2 = 6 * y - 4)
    (h₁ : 2 * x * y - 4 * x * z + 4 * y * z = y^2 + 5) :
    (x = 1 ∧ y = 3 ∧ z = 1) ∨ (x = 2 ∧ y = 3 ∧ z = 1 / 2) := by

  have h2 : x^2 + (y - 3) ^ 2 + 4 * z^2 = 5 := by
    nlinarith
  
  have hw : (y - x - 2 * z) ^ 2 + (y - 3) ^ 2 = 0 := by 
    nlinarith [h₀, h₁, sq_nonneg (y - x - 2 * z), sq_nonneg (y - 3)]
  
  have hy1 : (y - 3) ^ 2 = 0 := by 
    linarith [sq_nonneg (y - x - 2 * z), sq_nonneg (y - 3), hw]

  have hy2 : y - 3 = 0 := by 
    rw [sq_eq_zero_iff] at hy1 
    exact hy1
  
  have hy : y = 3 := by 
    linarith

  have h2z2 : y - x - 2 * z = 0 := by 
    have h2z : (y - x - 2 * z) ^ 2 = 0 := by 
      linarith [sq_nonneg (y - x - 2 * z), sq_nonneg (y - 3), hw]
    have h2z2 : y - x - 2 * z = 0 := by 
      rw [sq_eq_zero_iff] at h2z 
      exact h2z 
    exact h2z2
  
  rw [hy] at h2z2 
  have hx1 : x = 3 - 2 * z := by 
    linarith 

  have h_eq : x^2 + 4 * z^2 = 5 := by 
    rw [hy] at h2 
    nlinarith 

  rw [hx1] at h_eq 
  have hz : (z - 1) * (2 * z - 1) = 0 := by 
    nlinarith 

  cases' (mul_eq_zero.mp hz) with hz1 hz2 
  · 
    have hz3 : z = 1 := by 
      linarith 
    have hx2 : x = 1 := by 
      rw [hz3] at hx1 
      linarith 
    left 
    exact ⟨hx2, hy, hz3⟩ 
  · 
    have hz4 : z = 1 / 2 := by 
      linarith 
    have hx3 : x = 2 := by 
      rw [hz4] at hx1 
      linarith 
    right 
    exact ⟨hx3, hy, hz4⟩