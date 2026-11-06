import Mathlib

theorem number_theory_201120 (x y z : ℤ) :
    IsSquare (((x - y)^4 + (y - z)^4 + (z - x)^4) / 2) := by 
  have h1 : ((x - y)^4 + (y - z)^4 + (z - x)^4) / 2 = (x^2 + y^2 + z^2 - x * y - y * z - z * x) ^ 2 := by
    ring_nf
    <;> omega
  rw [h1]
  exact ⟨x^2 + y^2 + z^2 - x * y - y * z - z * x, by ring⟩