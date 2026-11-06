import Mathlib

theorem number_theory_209211 (n : ℕ) (hn : n > 1) :
    ∃ a b c d : ℕ, a + b = 4 * n ∧ c + d = 4 * n ∧ a * b - c * d = 4 * n := by
  have h1 : n > 1 := hn
  have h2 : n ≥ 2 := by omega
  use n + 1
  use 3 * n - 1
  use n - 1
  use 3 * n + 1
  constructor
  · -- Show that a + b = 4 * n
    omega
  constructor
  · -- Show that c + d = 4 * n
    omega
  · -- Show that a * b - c * d = 4 * n
    have h4 : (n + 1) * (3 * n - 1) = 4 * n + (n - 1) * (3 * n + 1) := by
      cases n with
      | zero => 
        omega 
      | succ n => 
        cases n with 
        | zero => 
          omega 
        | succ n => 
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_sub, Nat.sub_mul, mul_add, mul_comm]
          <;> ring_nf
          <;> omega
    have eq3 : (n + 1) * (3 * n - 1) = (n - 1) * (3 * n + 1) + 4 * n := by
      omega
    have eq4 : (n + 1) * (3 * n - 1) - ( (n - 1) * (3 * n + 1) ) = 4 * n := by
      have eq5 : (n + 1) * (3 * n - 1) = (n - 1) * (3 * n + 1) + 4 * n := eq3
      omega
    exact_mod_cast eq4