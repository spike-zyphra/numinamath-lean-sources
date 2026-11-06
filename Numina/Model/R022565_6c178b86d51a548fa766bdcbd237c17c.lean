import Mathlib

theorem number_theory_287474 :
    ∃ n1 n2 : ℕ, n1 ≠ 1 ∧ n2 ≠ 1 ∧ n1 > 1 ∧ n2 > 1 ∧
      IsSquare ((∑ i in Finset.Icc 1 n1, i^2) / n1) ∧
      IsSquare ((∑ i in Finset.Icc 1 n2, i^2) / n2) := by

  use 337, 337
  constructor
  · -- Show n1 ≠ 1
    norm_num
  constructor
  · -- Show n2 ≠ 1
    norm_num
  constructor
  · -- Show n1 > 1
    norm_num
  constructor
  · -- Show n2 > 1
    norm_num
  constructor
  · -- Show that the average of n1 is a perfect square
    native_decide
  · -- Show that the average of n2 is a perfect square
    native_decide