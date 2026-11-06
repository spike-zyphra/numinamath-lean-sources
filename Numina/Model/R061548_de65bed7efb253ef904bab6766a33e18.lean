import Mathlib

open Real
open scoped BigOperators

theorem number_theory_45813 (m : ℤ) :
  ∃ k : ℤ, m/3 + m^2/2 + m^3/6 = k := by 
  refine ⟨m/3 + m^2/2 + m^3/6, rfl⟩