import Mathlib

theorem algebra_176557 (v1 v2 t1 t2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h'' : t1 > 0) (h''' : t2 > 0) (h1 : 1 / v1 = 1 / v2 + t1 / 60) (h2 : 1 / v2 = 1 / v1 + t2 / 60)
    (h3 : 1 / (v1 + v2) = 1 / v1 + t1 / 60 ∧ 1 / (v1 + v2) = 1 / v2 + t2 / 60) :
    v1 = 60 * v2 * t2 / (t1 * v2 - t2 * v1) := by 
  have eq1 : 1 / v1 - 1 / v2 = t1 / 60 := by linarith
  have eq2 : 1 / v2 - 1 / v1 = t2 / 60 := by linarith
  have eq3 : (t1 : ℝ) + (t2 : ℝ) = (0 : ℝ) := by 
    have eq4 : (1 / v1 - 1 / v2 : ℝ) = (t1 / 60 : ℝ) := by 
      linarith [h1]
    have eq5 : (1 / v2 - 1 / v1 : ℝ) = (t2 / 60 : ℝ) := by 
      linarith [h2]
    have eq6 : (1 / v2 - 1 / v1 : ℝ) = -(1 / v1 - 1 / v2 : ℝ) := by ring
    have eq7 : (t2 / 60 : ℝ) = -(t1 / 60 : ℝ) := by 
      rw [show (1 / v1 - 1 / v2 : ℝ) = (t1 / 60 : ℝ) by 
        linarith [h1]
      ] at eq6 
      linarith [eq5, eq6]
    have eq8 : (t2 : ℝ) = -(t1 : ℝ) := by 
      linarith 
    linarith 
  nlinarith