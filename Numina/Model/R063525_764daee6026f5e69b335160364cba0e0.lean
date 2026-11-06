import Mathlib

theorem algebra_194238 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a = b + 3) (h2 : 1 / a + 1 / b = 3 / 20) :
    a = 15 := by 
  have h3 : a * b ≠ 0 := by
    apply mul_ne_zero
    linarith
    linarith
  
  have eq2 : a + b = (3 / 20) * (a * b) := by
    field_simp [h3] at h2 ⊢ 
    linarith
  
  rw [h1] at eq2
  
  have h_eq : 3 * b ^ 2 - 31 * b - 60 = 0 := by
    nlinarith
  
  have h5 : (b - 12) * (3 * b + 5) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp h5) with h6 h7
  
  · -- Case where b = 12
    have hb12 : b = 12 := by linarith
    have ha15 : a = 15 := by 
      rw [hb12] at h1
      linarith
    exact ha15
  
  · -- Case where 3b + 5 = 0, so b = -5/3 < 0 contradicts b > 0 
    have h8 : b < 0 := by 
      nlinarith
    linarith