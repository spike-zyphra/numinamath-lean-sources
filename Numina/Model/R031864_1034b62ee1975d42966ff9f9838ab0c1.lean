import Mathlib

theorem number_theory_111776 : Odd (∑ i in Finset.range 994, (-1 : ℚ)^i * (i + 1)) := by 
  have h1 : ∑ i in Finset.range 994, (-1 : ℚ)^i * (i + 1) = (-497 : ℚ) := by
    native_decide
  rw [h1]
  use -249
  norm_num