import Mathlib

theorem number_theory_165621 (N : ℕ) :
    ∃ k, k ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 k).length = 4 ∧
      (Nat.digits 10 k).toFinset = {1, 9, 8, 4} ∧
      7 ∣ N + k := by 
  have h1 : ∃ k, k ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 k).length = 4 ∧
      (Nat.digits 10 k).toFinset = {1, 9, 8, 4} ∧ 7 ∣ N + k := by 
    have h1 : N % 7 = 0 ∨ N % 7 = 1 ∨ N % 7 = 2 ∨ N % 7 = 3 ∨ N % 7 = 4 ∨ N % 7 = 5 ∨ N % 7 = 6 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1)
    · -- Case where N % 7 = 0
      use 9184
      constructor
      · -- Show 9184 ∈ [1000, 9999]
        native_decide
      constructor
      · -- Show (Nat.digits 10 9184).length = 4
        native_decide
      constructor
      · -- Show (Nat.digits 10 9184).toFinset = {1, 9, 8, 4}
        native_decide
      · -- Show 7 divides N + 9184
        omega 
    · -- Case where N % 7 = 1
      use 9148
      constructor
      · -- Show 9148 ∈ [1000, 9999]
        native_decide
      constructor
      · -- Show (Nat.digits 10 9148).length = 4
        native_decide
      constructor 
      · -- Show (Nat.digits 10 9148).toFinset = {1, 9, 8, 4}
        native_decide
      · -- Show 7 divides N + 9148 
        omega
    · -- Case where N % 7 = 2 
      use 1489
      constructor 
      · -- Show 1489 ∈ [1000, 9999]
        native_decide
      constructor
      · -- Show (Nat.digits 10 1489).length = 4 
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 1489).toFinset = {1, 9, 8, 4} 
        native_decide 
      · -- Show 7 divides N + 1489 
        omega 
    · -- Case where N % 7 = 3 
      use 8194 
      constructor 
      · -- Show 8194 ∈ [1000, 9999]
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 8194).length = 4 
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 8194).toFinset = {1, 9, 8, 4} 
        native_decide 
      · -- Show 7 divides N + 8194 
        omega 
    · -- Case where N % 7 = 4 
      use 4819 
      constructor 
      · -- Show 4819 ∈ [1000, 9999]
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 4819).length = 4 
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 4819).toFinset = {1, 9, 8, 4} 
        native_decide 
      · -- Show 7 divides N + 4819 
        omega 
    · -- Case where N % 7 = 5 
      use 8941
      constructor 
      · -- Show 8941 ∈ [1000, 9999]
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 8941).length = 4 
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 8941).toFinset = {1, 9, 8, 4} 
        native_decide 
      · -- Show 7 divides N + 8941 
        omega 
    · -- Case where N % 7 = 6 
      use 8149 
      constructor 
      · -- Show 8149 ∈ [1000, 9999]
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 8149).length = 4 
        native_decide 
      constructor 
      · -- Show (Nat.digits 10 8149).toFinset = {1, 9, 8, 4} 
        native_decide 
      · -- Show 7 divides N + 8149 
        omega 
  exact h1