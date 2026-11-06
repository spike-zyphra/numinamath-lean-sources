import Mathlib

theorem algebra_196850 (B G Y : ℕ) (hB : B ≤ 38) (hG : G ≤ 38) (hY : Y ≤ 38)
    (h1 : B + G + Y = 38) (h2 : G = 2 * Y) (h3 : B = G + 6) :
    B = 27 ∧ G = 33 ∧ Y = 16 := by 
  have h4 : B = 2 * Y + 6 := by 
    rw [h2] at h3
    omega 
  have h5 : 5 * Y = 32 := by 
    omega 
  have h6 : Y = 0 := by 
    omega 
  omega