import Mathlib

theorem algebra_10566 {x1 x2 : ℝ} (hx1 : 8*x1^2+12*x1-14=0) (hx2 : 8*x2^2+12*x2-14=0) (hne : x1 ≠ x2) : x1^2+x2^2=23/4 := by
  have h1 : 8 * (x1^2 - x2^2) + 12 * (x1 - x2) = 0 := by
    linarith [hx1, hx2]
  
  have h2 : (x1 - x2) * (8 * (x1 + x2) + 12) = 0 := by
    ring_nf at h1 ⊢ 
    linarith
  
  have h3 : 8 * (x1 + x2) + 12 = 0 := by
    apply (mul_left_inj' (show x1 - x2 ≠ 0 by
      intro h
      apply hne
      linarith
    )).mp 
    linarith
  
  have h4 : x1 + x2 = -3/2 := by 
    linarith
  
  have h5 : 8 * (x1^2 + x2^2) + 12 * (x1 + x2) - 28 = 0 := by
    nlinarith [hx1, hx2]
  
  rw [h4] at h5
  
  linarith