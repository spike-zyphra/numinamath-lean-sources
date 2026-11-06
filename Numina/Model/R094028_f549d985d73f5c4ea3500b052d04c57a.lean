import Mathlib

theorem number_theory_253847 (S : Finset ℕ) (hS : ∀ n ∈ S, n > 0) :
    ∃ T : Finset ℕ, T ⊆ S ∧ ∀ m ∈ T, ∀ n ∈ T, m ≠ n → Nat.gcd m n = Nat.gcd n m ∧
      Nat.lcm m n = Nat.lcm n m := by 
  use ∅ 
  simp