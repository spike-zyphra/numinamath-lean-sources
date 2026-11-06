import Mathlib

theorem number_theory_221137 (n : ℕ) (hn : n = 2004) :
    ∃ s : Finset ℕ, (∀ i ∈ s, i > 0) ∧ ∑ i ∈ s, i = ∏ i ∈ s, i := by 
  use {2, 2}
  constructor
  · -- Show that all elements in s are positive
    intro i hi
    fin_cases hi <;> simp <;> omega
  · -- Show that the sum of the elements in s is equal to the product of the elements in s
    simp [Finset.sum_insert, Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton]
    <;> try rfl
    <;> try simp [add_assoc, mul_add, add_comm, add_left_comm]
    <;> tauto