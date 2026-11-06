import Mathlib
theorem number_theory_606072 : ∃ A B : Finset ℕ, A.card = 3 ∧ B.card = 3 ∧ (∀ a ∈ A, a > 2003) ∧ (∀ b ∈ B, b > 2003) ∧ A ∩ B = ∅ ∧
∑ a ∈ A, a = ∑ b ∈ B, b ∧ ∑ a ∈ A, a ^ 2 = ∑ b ∈ B, b ^ 2:= by
  use {2004, 2008, 2009}
  use {2005, 2006, 2010}
  constructor
  · -- Show that the set A has 3 elements
    native_decide
  constructor
  · -- Show that the set B has 3 elements
    native_decide
  constructor
  · -- Show that ∀ a ∈ A, a > 2003
    intro a ha
    fin_cases ha <;> norm_num
  constructor
  · -- Show that ∀ b ∈ B, b > 2003
    intro b hb
    fin_cases hb <;> norm_num
  constructor
  · -- Show that A ∩ B = ∅
    native_decide
  constructor
  · -- Show that ∑ a ∈ A, a = ∑ b ∈ B, b
    native_decide
  · -- Show that ∑ a ∈ A, a ^ 2 = ∑ b ∈ B, b ^ 2
    native_decide