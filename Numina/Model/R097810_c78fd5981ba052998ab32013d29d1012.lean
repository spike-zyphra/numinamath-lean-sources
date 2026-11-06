import Mathlib

theorem number_theory_7640 (a b : ℤ) (_ : 0 < a) (h₂ : 0 < b)
    (hcoprime : IsCoprime a b) :
    ∃ x y, a * x - b * y = 1 := by 
  obtain ⟨x, y, hxy⟩ := hcoprime
  refine ⟨x, -y, by linarith⟩