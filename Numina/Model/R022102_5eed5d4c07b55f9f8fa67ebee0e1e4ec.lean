import Mathlib

theorem number_theory_149978 : ¬∃ x y z : ℤ, (x - y)^3 + (y - z)^3 + (z - x)^3 = 2021 := by
  rintro ⟨x, y, z, h⟩
  have h1 : (x - y : ℤ)^3 + (y - z)^3 + (z - x)^3 = 3 * ((x - y) * (y - z) * (z - x)) := by 
    ring 
  rw [h1] at h 
  omega