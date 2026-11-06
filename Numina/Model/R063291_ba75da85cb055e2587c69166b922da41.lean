import Mathlib

theorem number_theory_144231 (p : ℕ) (h : Even p) :
    Even (p^2) := by 
  obtain ⟨m, hm⟩ := h 
  use 2 * m^2 
  rw [hm]
  ring