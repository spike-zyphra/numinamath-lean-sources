import Mathlib

theorem number_theory_196928 (n : ℕ) (hn : n > 1) :
    ∃ a b c d, a + b = 4 * n ∧ c + d = 4 * n ∧ a * b - c * d = 4 * n := by
  use n + 1, 3 * n - 1, n - 1, 3 * n + 1
  constructor
  · -- Show that a + b = 4 * n
    omega 
  constructor
  · -- Show c + d = 4 * n
    omega
  · -- Show that a * b - c * d = 4 * n
    have h1 : n ≥ 2 := by omega
    have h5 : (n + 1 : ℕ) * (3 * n - 1 : ℕ) = (n - 1 : ℕ) * (3 * n + 1 : ℕ) + 4 * n := by
      cases n with
      | zero => 
        omega 
      | succ n => 
        cases n with
        | zero => 
          omega
        | succ n => 
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.add_assoc]
          <;> ring_nf
          <;> omega 
    have h8 : (n + 1 : ℕ) * (3 * n - 1 : ℕ) ≥ (n - 1 : ℕ) * (3 * n + 1 : ℕ) := by 
      nlinarith [h5]
    omega