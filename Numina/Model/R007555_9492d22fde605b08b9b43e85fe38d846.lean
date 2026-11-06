import Mathlib

theorem Algebra_696 (x1 x2 x3 x4 x5 : ℝ) (h1 : 2*x1+x2+x3+x4+x5=6) (h2 : x1+2*x2+x3+x4+x5=12) (h3 : x1+x2+2*x3+x4+x5=24) (h4 : x1+x2+x3+2*x4+x5=48) (h5 : x1+x2+x3+x4+2*x5=96) : 3*x4+2*x5 = 181 := by
  have eq1 : x2 = x1 + 6 := by 
    linarith
  have eq2 : x3 = x2 + 12 := by 
    nlinarith [h1, h2, h3]
  have eq3 : x4 = x3 + 24 := by 
    nlinarith [h1, h2, h3, h4]
  have eq4 : x5 = x4 + 48 := by 
    nlinarith [h1, h2, h3, h4, h5]
  have hx1 : x1 = -25 := by
    nlinarith [h1, eq1, eq2, eq3, eq4]
  have hx4 : x4 = 17 := by
    nlinarith [hx1, eq1, eq2, eq3, eq4]
  have hx5 : x5 = 65 := by
    nlinarith [hx1, eq1, eq2, eq3, eq4]
  linarith [hx4, hx5]