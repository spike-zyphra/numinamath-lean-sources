import Mathlib

theorem algebra_1427 (x y z : ℝ) (h₀ : (8*x-2*y+z)/5=(6*x+z)/3-(x+y)/2)
    (h₁ : (x+y+z)/3+(x-1)/5=(y+1)/3) (h₂ : 3*x+4*y=5*z-1) :
    1989*x-y+25*z=1990 := by
  have h3 : 3 * x + 3 * y - 4 * z = 0 := by
    linarith
  have h4 : 8 * x + 5 * z = 8 := by
    linarith
  have h5 : z = 0 := by
    linarith [h3, h4, h₂]
  have h6 : x = 1 := by
    linarith [h4, h5]
  have h7 : y = -1 := by
    linarith [h3, h5, h6]
  linarith [h6, h7, h5]