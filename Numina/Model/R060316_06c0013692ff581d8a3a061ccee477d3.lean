import Mathlib

theorem algebra_155740 (a : ℝ) (h : ∃ x y, x ≠ y ∧ x^3-4*x^2-17*x+a=0 ∧ y^3-4*y^2-17*y+a=0 ∧ x+y=1) :
    a=60 := by
  rcases h with ⟨x, y, hxy, hx, hy, hxy1⟩
  have eq2 : x^3 - y^3 -4 * (x^2 - y^2) -17 * (x - y) = 0 := by
    have h1 : x^3 - 4 * x^2 - 17 * x + a = 0 := by linarith
    have h2 : y^3 - 4 * y^2 - 17 * y + a = 0 := by linarith
    nlinarith 
  have eq3 : (x - y) * (x^2 + x * y + y^2 - 4 * (x + y) - 17) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), hxy1, sq_nonneg (x - 5), sq_nonneg (y - 5), sq_nonneg (x + 4), sq_nonneg (y + 4)]
  
  cases' (mul_eq_zero.mp eq3) with hxy2 hxy3

  · -- Case where x - y = 0, which means x = y, contradicting x ≠ y
    exfalso
    exact hxy (by linarith)
  
  · -- Case where the second factor is zero
    have eq4 : x^2 + x * y + y^2 = 21 := by
      nlinarith [hxy1, hxy3]
    
    have eq5 : y = 1 - x := by 
      nlinarith 

    rw [eq5] at eq4
    have eq6 : x^2 - x - 20 = 0 := by
      nlinarith [eq4]

    have eq7 : (x - 5) * (x + 4) = 0 := by
      nlinarith

    cases' (mul_eq_zero.mp eq7) with hx1 hx2
    · -- When x =5, y=-4
      have hx_eq5 : x = (5 : ℝ) := by linarith
      have hy_eq4 : y = (-4 : ℝ) := by 
        nlinarith [eq5, hx_eq5]
      rw [hx_eq5] at hx
      rw [hy_eq4] at hy
      nlinarith

    · -- When x = -4, y =5
      have hx_eq4 : x = (-4 : ℝ) := by linarith
      have hy_eq5 : y = (5 : ℝ) := by 
        nlinarith [eq5, hx_eq4]
      rw [hx_eq4] at hx
      rw [hy_eq5] at hy
      nlinarith