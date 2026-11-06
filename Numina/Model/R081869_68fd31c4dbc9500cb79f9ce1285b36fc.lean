import Mathlib

theorem algebra_322011 (x y z : ℝ) (h : 2*x+4*y=220) (h' : 3*x+8*y+z=441.2)
    (h'' : 2*x+6*y+z=116) :
    z=150 := by 
  have eq1 : x = 110 - 2 * y := by 
    linarith 
  rw [eq1] at h' 
  have eq2 : 2 * y + z = 111.2 := by 
    ring_nf at h' ⊢ 
    linarith 
  rw [eq1] at h'' 
  have eq3 : 2 * y + z = -104 := by 
    ring_nf at h'' ⊢ 
    linarith 
  linarith