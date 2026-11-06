import Mathlib

theorem number_theory_210702 : 1003 ∣ ∑ i ∈ Finset.range 2005, (-1 : ℤ) ^ i * (i + 1) ^ 2006 ∧ ¬(2006 ∣ ∑ i ∈ Finset.range 2005, (-1 : ℤ) ^ i * (i + 1) ^ 2006) := by 
  native_decide