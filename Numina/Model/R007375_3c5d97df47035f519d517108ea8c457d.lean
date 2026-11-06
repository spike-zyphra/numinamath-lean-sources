import Mathlib

theorem number_theory_15654 (s : Finset ℕ) (hs : s = (Finset.Icc 1 10).image fun n => n ^ 2 % 11) :
    (∑ i ∈ s, i) / 11 = 2 := by 
  rw [hs]
  native_decide