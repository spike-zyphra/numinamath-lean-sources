import Mathlib

def star (a b c d : ℤ) := (a - c, b + d)

theorem algebra_96102 {x y : ℤ} (h : star 3 3 0 0 = star x y 3 2) :
    x = 6 := by 
  have eq1 : (3 : ℤ) = x - 3 := by 
    rw [show star 3 3 0 0 = (3 - (0 : ℤ), 3 + (0 : ℤ)) by rfl] at h
    rw [show star x y 3 2 = (x - (3 : ℤ), y + (2 : ℤ)) by rfl] at h
    simp [Prod.ext_iff] at h 
    omega 
  have eq2 : (3 : ℤ) = y + 2 := by 
    rw [show star 3 3 0 0 = (3 - (0 : ℤ), 3 + (0 : ℤ)) by rfl] at h
    rw [show star x y 3 2 = (x - (3 : ℤ), y + (2 : ℤ)) by rfl] at h
    simp [Prod.ext_iff] at h 
    omega 
  omega