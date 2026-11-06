import Mathlib

theorem number_theory_308709 :
    ∃ k : ℕ, k = 7 ∧ ∃ s : Finset ℕ, s.card = k ∧ ∑ p ∈ s, p^2 = 2010 ∧ ∀ p ∈ s, Nat.Prime p := by 
  use 7
  constructor
  · rfl
  use { 2, 3, 7, 11, 13, 17, 37 }
  constructor
  · -- Show that the cardinality of the set {2, 3, 7, 11, 13, 17, 37} is 7
    native_decide
  constructor
  · -- Show that the sum of the squares of the elements in the set {2, 3, 7, 11, 13, 17, 37} is 2010
    native_decide
  · -- Show that all elements in the set {2, 3, 7, 11, 13, 17, 37} are prime
    intro p hp
    fin_cases hp <;> norm_num