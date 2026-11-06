import Mathlib

theorem number_theory_105222 :
    IsSquare (2 * ∑ i ∈ Finset.Icc 1 2016, i - 2016) ∧
    ¬IsSquare (∑ i ∈ Finset.Icc 1 2016, ∏ j ∈ Finset.Icc 1 i, j) := by 
  constructor 
  · -- Show that $a$ is a perfect square
    native_decide 
  · -- Show that b is not a perfect square
    native_decide