import Mathlib

theorem number_theory_199375 (x y z t : ℤ) (h : x + y = z + t) :
    ∃ a b c, a^2 + b^2 + c^2 = x^2 + y^2 + z^2 + t^2 := by
  have ht : t = x + y - z := by 
    omega
  use x + y, y - z, z - x
  rw [ht]
  ring