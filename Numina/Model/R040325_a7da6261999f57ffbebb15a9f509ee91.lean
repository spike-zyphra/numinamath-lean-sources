import Mathlib

theorem number_theory_127103 :
    ∃ s : Finset ℕ, s.card = 5 ∧
      (∀ n ∈ s, ¬(3 ∣ n)) ∧
      (∀ n ∈ s, ¬(4 ∣ n)) ∧
      (∀ n ∈ s, ¬(5 ∣ n)) ∧
      (∀ t ⊆ s, t.card = 3 → 3 ∣ ∑ n ∈ t, n) ∧
      (∀ t ⊆ s, t.card = 4 → 4 ∣ ∑ n ∈ t, n) ∧
      5 ∣ ∑ n ∈ s, n := by
  use {1, 61, 121, 181, 241}
  constructor
  · -- Show the set s has 5 elements
    native_decide
  constructor
  · -- Show that no element in s is divisible by 3
    intro n hn
    fin_cases hn <;> norm_num
  constructor
  · -- Show that no element in s is divisible by 4
    intro n hn
    fin_cases hn <;> norm_num
  constructor
  · -- Show that no element in s is divisible by 5
    intro n hn
    fin_cases hn <;> norm_num
  constructor
  · -- Show that the sum of any 3 elements in s is divisible by 3
    intro t ht ht3
    have h1 : t ⊆ ({1, 61, 121, 181, 241} : Finset ℕ) := ht
    have h2 : t.card = 3 := ht3
    have h3 : t ∈ (Finset.powerset ({1, 61, 121, 181, 241} : Finset ℕ)) := by
      simp
      tauto
    fin_cases h3 <;> simp at * <;> try { try omega }
    <;> try { contradiction }
  constructor
  · -- Show that the sum of any 4 elements in s is divisible by 4
    intro t ht ht4
    have h1 : t ⊆ ({1, 61, 121, 181, 241} : Finset ℕ) := ht
    have h2 : t.card = 4 := ht4
    have h3 : t ∈ (Finset.powerset ({1, 61, 121, 181, 241} : Finset ℕ)) := by
      simp
      tauto
    fin_cases h3 <;> simp at * <;> try { try omega }
    <;> try { contradiction }
  · -- Show that the sum of all 5 elements is divisible by 5
    native_decide