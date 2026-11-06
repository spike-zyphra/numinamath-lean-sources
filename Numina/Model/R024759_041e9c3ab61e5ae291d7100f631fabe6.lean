import Mathlib

theorem number_theory_13297 :
    IsGreatest {n | ∃(k : ℕ), 0 < k ∧ (n : ℕ) = Nat.factorization (Nat.factorial 2022) 7} 334 := by
  constructor
  · -- Show 334 is in the set
    use 1
    constructor
    · -- Show k > 0
      norm_num
    · -- Show 334 = Nat.factorization (Nat.factorial 2022) 7
      native_decide
  · -- Show no greater element is in the set
    intro n hn
    rcases hn with ⟨k, hk_pos, h_eq⟩
    have h1 : (n : ℕ) = Nat.factorization (Nat.factorial 2022) 7 := by
      exact_mod_cast h_eq
    have h2 : Nat.factorization (Nat.factorial 2022) 7 = 334 := by
      native_decide
    have h_eq' : n = 334 := by
      omega
    omega