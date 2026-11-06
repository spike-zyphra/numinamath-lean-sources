import Mathlib

theorem algebra_321173 {x y : ℝ} (h1 : x^3 + x^3 * y^3 + y^3 = 17) (h2 : x + x * y + y = 5) :
    (x, y) = (1, 2) ∨ (x, y) = (2, 1) := by
  have eq1 : x + y + x * y = 5 := by 
    nlinarith 
  have eq2 : x^3 + x^3 * y^3 + y^3 = (x + y)^3 - 3 * (x * y) * (x + y) + (x * y)^3 := by 
    ring
  rw [eq2] at h1 
  have eq3 : x + y = 5 - x * y := by 
    nlinarith 
  rw [eq3] at h1 
  have h4 : (x * y - 2) * (x * y - 3) = 0 := by
    nlinarith [sq_nonneg (x * y - 2), sq_nonneg (x * y - 3), sq_nonneg ((5 - x * y) - 3), sq_nonneg ((5 - x * y) - 2)]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- x * y = 2 
    have h7 : x * y = 2 := by 
      linarith 
    have h8 : x + y = 3 := by 
      nlinarith 
    have h9 : (x - 1) * (x - 2) = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (x - y), sq_nonneg ((x * y) - 2)]
    cases' (mul_eq_zero.mp h9) with h10 h11 
    · -- x - 1 = 0 
      have hx1 : x = 1 := by 
        linarith 
      have hy1 : y = 2 := by 
        rw [hx1] at h7 
        nlinarith 
      left 
      simp [hx1, hy1] 
    · -- x - 2 = 0 
      have hx2 : x = 2 := by 
        linarith 
      have hy2 : y = 1 := by 
        rw [hx2] at h7 
        nlinarith 
      right 
      simp [hx2, hy2] 
  · -- x * y = 3 
    have h7 : x * y = 3 := by 
      linarith 
    have h8 : x + y = 2 := by 
      nlinarith 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]