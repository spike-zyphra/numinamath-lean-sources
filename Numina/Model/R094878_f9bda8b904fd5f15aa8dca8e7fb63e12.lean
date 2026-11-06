import Mathlib

theorem algebra_6452 {f : ℝ → ℝ} (a b c : ℝ) (hf : f = fun x => a * x ^ 2 + b * x + c)
    (h1 : f (-4) = 7) (h2 : f 4 = 23) (h3 : f (-1) = 6) : f 1 = 10 := by 
  have eq1 : a * (-4 : ℝ) ^ 2 + b * (-4 : ℝ) + c = 7 := by 
    rw [hf] at h1
    simpa using h1
  have eq2 : a * (4 : ℝ) ^ 2 + b * (4 : ℝ) + c = 23 := by 
    rw [hf] at h2
    simpa using h2
  have eq3 : a * (-1 : ℝ) ^ 2 + b * (-1 : ℝ) + c = 6 := by 
    rw [hf] at h3
    simpa using h3
  have eq4 : b = 2 := by
    nlinarith
  have eq5 : a + c = 8 := by
    rw [eq4] at eq3
    nlinarith
  have eq6 : 16 * a + c = 15 := by
    rw [eq4] at eq1
    nlinarith
  have ha : a = 7 / 15 := by 
    linarith
  have hc : c = 113 / 15 := by
    linarith
  have eq7 : f 1 = a * (1 : ℝ) ^ 2 + b * (1 : ℝ) + c := by 
    rw [hf]
  rw [eq7]
  rw [ha, eq4, hc]
  norm_num