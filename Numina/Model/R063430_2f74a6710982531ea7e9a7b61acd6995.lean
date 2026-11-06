import Mathlib

theorem number_theory_145843 : ∃ n : ℕ, n > 0 ∧ ∑ i ∈ Finset.range 100, (n + i) = 1627384950 := by 
  use 16273800
  constructor
  · -- Show n > 0
    norm_num
  · -- Show that the sum equals the given value
    native_decide