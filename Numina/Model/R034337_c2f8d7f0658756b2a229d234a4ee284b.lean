import Mathlib

theorem system_of_quadratic_equations_solution {x y : ℝ} 
    (h1 : 8*x^2 - 26*x*y + 15*y^2 + 116*x - 150*y + 360 = 0)
    (h2 : 8*x^2 + 18*x*y - 18*y^2 + 60*x + 45*y + 108 = 0) :
    (x, y) ∈ ({(0, 4), (-15/2, 1), (-9/2, 0)} : Set (ℝ × ℝ)) := by
  have eq1 : (4 * x - 3 * y + 18) * (2 * x - 5 * y + 20) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp eq1) with h3 h4
  · -- Case h3 : 4 * x - 3 * y + 18 = 0 
    have hy : y = (4 * x + 18) / 3 := by
      linarith 
    rw [hy] at h2
    have h5 : (x + 9 / 2) = 0 := by
      nlinarith 
    have hx1 : x = -9 / 2 := by linarith
    have hy1 : y = 0 := by 
      rw [hx1] at hy 
      linarith 
    simp [hx1, hy1] 
  · -- Case h4 : 2 * x - 5 * y + 20 = 0
    have hy : y = (2 * x + 20) / 5 := by
      linarith 
    rw [hy] at h2
    have : x * (308 / 25 * x + 462 / 5) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp this) with hx2 hx3 
    · -- Case hx2 : x = 0 
      have hx1 : x = 0 := by linarith 
      have hy1 : y = 4 := by 
        rw [hx1] at hy 
        linarith 
      simp [hx1, hy1] 
    · -- Case hx3 : 308 / 25 * x + 462 / 5 = 0 
      have hx4 : x = -15 / 2 := by 
        nlinarith 
      have hy2 : y = 1 := by 
        rw [hx4] at hy 
        linarith 
      simp [hx4, hy2]