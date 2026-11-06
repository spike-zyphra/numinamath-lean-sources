import Mathlib

theorem number_theory_217182 : ∃ s : Finset ℕ, ∑ n ∈ s, (2013 - n)^2 = 2013 := by
  use {1969, 2005, 2010, 2011}
  native_decide