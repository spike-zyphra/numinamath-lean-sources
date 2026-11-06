import Mathlib

theorem number_theory_40046 (n : ℤ) (h : ∃ x y z : ℤ, x^2 + y^2 + z^2 - x * y - y * z - z * x = n) :
    ∃ x y : ℤ, x^2 + y^2 - x * y = n := by 
  rcases h with ⟨x, y, z, h_eq⟩
  refine ⟨x - z, y - z, by 
    nlinarith
  ⟩