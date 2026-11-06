import Mathlib

theorem number_theory_47688 : ∃ s : Finset ℕ, s.card = 9 ∧
    (∀ n ∈ s, n ∈ Finset.Icc 16 30) ∧
    ∏ n ∈ s, n = Nat.factorial 15 := by 
  use {16, 18, 20, 21, 22, 25, 26, 27, 28}
  constructor
  · -- Show that s has cardinality 9
    native_decide
  constructor
  · -- Show that ∀ n ∈ s, n ∈ Finset.Icc 16 30
    intro n hn
    fin_cases hn <;> simp [Finset.mem_Icc] <;> all_goals omega
  · -- Show that the product of elements in s equals 15!
    native_decide