import Mathlib

theorem algebra_176510 {x y : ℕ} (hx : x + y = 90) (hxy : (40 / 100 : ℝ) * x = (30 / 100 : ℝ) * y + 15) :
    max x y = 60 := by
  have h1 : (x : ℝ) + (y : ℝ) = (90 : ℝ) := by
    exact_mod_cast hx
  have h2 : (x : ℝ) = 60 := by 
    have eq1 : (x : ℝ) + (y : ℝ) = (90 : ℝ) := by exact_mod_cast hx
    have eq2 : (40 / 100 : ℝ) * (x : ℝ) = (30 / 100 : ℝ) * (y : ℝ) + 15 := by 
      exact_mod_cast hxy
    have h3 : (y : ℝ) = (90 : ℝ) - (x : ℝ) := by 
      linarith
    rw [h3] at eq2
    linarith
  have hx2 : x = 60 := by
    exact_mod_cast h2
  have hy2 : y = 30 := by 
    omega
  rw [hx2, hy2]
  norm_num