import Mathlib

theorem number_theory_140543 :
    ∃ n : ℕ, n ∈ Finset.Icc 10000 99999 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧
      ∃ p q : ℕ, p ∈ Finset.Icc 1000 9999 ∧ q ∈ Finset.Icc 1000 9999 ∧ Nat.digits 10 p = List.reverse (Nat.digits 10 p) ∧
        Nat.digits 10 q = List.reverse (Nat.digits 10 q) ∧ n = p + q := by 
  use 11011
  constructor
  · -- Show that 11011 is in the range [10000, 99999]
    norm_num [Finset.mem_Icc]
  constructor
  · -- Show that 11011 is a palindrome
    native_decide
  · -- Show the existence of p and q
    use 5005, 6006
    constructor
    · -- Show that 5005 is in the range [1000, 9999]
      norm_num [Finset.mem_Icc]
    constructor
    · -- Show that 6006 is in the range [1000, 9999]
      norm_num [Finset.mem_Icc]
    constructor
    · -- Show that 5005 is a palindrome
      native_decide
    constructor
    · -- Show that 6006 is a palindrome
      native_decide
    · -- Show that 11011 = 5005 + 6006
      norm_num