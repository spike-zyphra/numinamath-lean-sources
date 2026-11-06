import Mathlib

theorem algebra_234932 {x y z : ℝ} (h1 : x + y - 2018 = (y - 2019) * x)
    (h2 : y + z - 2017 = (y - 2019) * z) (h3 : x + z + 5 = x * z) :
    (x, y, z) = (3, 2021, 4) ∨ (x, y, z) = (-1, 2019, -2) := by
  have hy : (y - 2019) * (y - 2019 - 2) = 0 := by 
    nlinarith [sq_nonneg (x - 3), sq_nonneg (z - 4), sq_nonneg (y - 2021), sq_nonneg (x + 1), sq_nonneg (z + 2), sq_nonneg (y - 2019)]
  cases' (mul_eq_zero.mp hy) with hy1 hy2
  · -- Case where $y - 2019 = 0$, so $y = 2019$
    have h_eq_y : y - 2019 = 0 := by 
      linarith 
    have h_eq1 : y = 2019 := by 
      linarith 
    have hx2 : x = -1 := by 
      rw [show y = 2019 by linarith] at h1
      nlinarith
    have h_eq3 : z = -2 := by 
      rw [show y = 2019 by linarith] at h2
      nlinarith
    right
    simp [hx2, h_eq1, h_eq3]
  · -- Case where $y - 2019 - 2 = 0$, so $y - 2019 = 2$ and $y = 2021$
    have hy_eq : y - 2019 = 2 := by
      linarith
    have hy_eq2 : y = 2021 := by 
      linarith 
    have hx1 : x = 3 := by
      rw [show y = 2021 by linarith] at h1
      nlinarith
    have h_eq4 : z = 4 := by 
      rw [show y = 2021 by linarith] at h2
      nlinarith 
    left 
    simp [hx1, hy_eq2, h_eq4]