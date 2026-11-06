import Mathlib

theorem number_theory_109325 :
    ∃ A B : Finset ℕ,
      A.card = 3 ∧
      B.card = 3 ∧
      (∀ x ∈ A, x > 2003) ∧
      (∀ m ∈ B, m > 2003) ∧
      A ∩ B = ∅ ∧
      ∑ x ∈ A, x = ∑ m ∈ B, m ∧
      ∑ x ∈ A, x^2 = ∑ m ∈ B, m^2 := by 
  use {2005, 2009, 2010}
  use {2006, 2007, 2011}
  constructor
  · -- Show that the cardinality of A is 3
    native_decide
  constructor
  · -- Show that the cardinality of B is 3
    native_decide
  constructor
  · -- Show that all elements in A are greater than 2003
    intro x hx
    fin_cases hx <;> norm_num
  constructor
  · -- Show that all elements in B are greater than 2003
    intro m hm
    fin_cases hm <;> norm_num
  constructor
  · -- Show that A and B have no common elements
    native_decide
  constructor
  · -- Show that the sum of A equals the sum of B
    native_decide
  · -- Show that the sum of squares of A equals the sum of squares of B
    native_decide