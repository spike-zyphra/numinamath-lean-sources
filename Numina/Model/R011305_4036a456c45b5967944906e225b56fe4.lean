import Mathlib

theorem algebra_2842 (a : ℝ) (x : ℝ) (h : x = 2) (h1 : (1/9) * ((1/6) * ((1/3) * ((x + a)/2 + 4) - 7) + 10) = 1) : a = -4 := by
  have h3 : (1/9) * ((1/6) * ((1/3) * (( (2: ℝ) + a)/2 + 4) - 7) + 10) = 1 := by
    rw [show x = (2 : ℝ) by linarith [h]] at h1
    linarith
  have eq2 : (1/9) * ((1/6) * ((1/3) * (( (2: ℝ) + a)/2 + 4) - 7) + 10) = (a + 328)/324 := by 
    field_simp
    ring 
  have eq3 : (a + 328)/324 = 1 := by
    linarith [h3, eq2]
  have eq4 : a + 328 = 324 := by
    linarith
  linarith