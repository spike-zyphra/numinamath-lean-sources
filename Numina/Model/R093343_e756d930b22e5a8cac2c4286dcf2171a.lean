import Mathlib

theorem algebra_259549 {x y : ℝ} (h1 : y^2 + x * y = 15) (h2 : x^2 + x * y = 10) :
    (x, y) = (2, 3) ∨ (x, y) = (-2, -3) := by 
  have h3 : (x + y) ^ 2 = 25 := by 
    nlinarith
  have h4 : (x + y) = 5 ∨ (x + y) = -5 := by 
    have h : (x + y) ^ 2 - 25 = 0 := by linarith
    have h5 : ((x + y) - 5) * ((x + y) + 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · left
      linarith
    · right
      linarith
  
  cases' h4 with h4 h4
  
  · -- case x + y = 5
    have hy : y = 5 - x := by linarith
    rw [hy] at h1 h2
    have hx : x = 2 := by 
      nlinarith
    have hy' : y = 3 := by
      linarith [h4, hx]
    left
    simp [hx, hy']
  
  · -- case x + y = -5
    have hy : y = -5 - x := by linarith
    rw [hy] at h1 h2
    have hx : x = -2 := by 
      nlinarith
    have hy' : y = -3 := by
      linarith [h4, hx]
    right
    simp [hx, hy']