import Mathlib

theorem algebra_123122 (x y z : ℝ) (h1 : 6*x-7*y-z-2=0) (h2 : x+7*y-4*z-5=0) :
    (x-1)/35=(y-4/7)/23 ∧ (y-4/7)/23=z/49 := by
  constructor
  · -- First part: Show (x - 1)/35 = (y - 4/7)/23
    have eq1 : 7 * x - 5 * z = 7 := by
      linarith [h1, h2]
    have eq2 : x - 1 = 5 / 7 * z := by 
      linarith
    have eq3 : 7 * y - 4 = 23 / 7 * z := by 
      have hx : x = 1 + 5 / 7 * z := by 
        linarith
      rw [hx] at h2
      linarith
    have eq4 : (x - 1) / 35 = (y - 4 / 7) / 23 := by 
      have h1 : x - 1 = 5 / 7 * z := by linarith
      have h2 : y - 4 / 7 = 23 / 49 * z := by 
        linarith [eq3]
      linarith
    linarith [eq4]
  · -- Second part: Show (y - 4/7)/23 = z/49
    have eq3 : 7 * y - 4 = 23 / 7 * z := by 
      have hx : x = 1 + 5 / 7 * z := by 
        linarith [h1, h2]
      rw [hx] at h2
      linarith
    have eq4 : (y - 4 / 7) / 23 = z / 49 := by 
      linarith [eq3]
    linarith [eq4]