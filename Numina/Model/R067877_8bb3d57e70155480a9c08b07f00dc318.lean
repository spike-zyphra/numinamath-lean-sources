import Mathlib

theorem algebra_235798 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x / y = 2 / 3) (h2 : y / (x + y) = 1 / 3) :
    x / (x + y) = 1 / 3 := by 
  have h3 : y ≠ 0 := by linarith 
  have h4 : x + y ≠ 0 := by 
    by_contra h
    have h5 : x = 0 := by linarith [h, show y > 0 from hy]
    linarith [h5, hx]

  have h5 : x = (2 / 3) * y := by 
    have h6 : x = (2 / 3) * y := by 
      field_simp [h3] at h1 ⊢
      linarith 
    linarith

  have h7 : 3 * y = x + y := by 
    field_simp [h4] at h2 ⊢
    linarith 

  have h8 : x = 2 * y := by 
    linarith

  have h9 : (2 / 3) * y = 2 * y := by 
    linarith [h5, h8]

  have h10 : y = 0 := by 
    nlinarith

  linarith [show y > 0 from hy, show y = 0 by linarith [h10]]