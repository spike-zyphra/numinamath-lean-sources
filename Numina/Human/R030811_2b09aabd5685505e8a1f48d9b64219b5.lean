import Mathlib

theorem number_theory_275876 (n : ℕ) (h : n > 0) :
    6 ∣ 2^n + 2^(n + 1) := by
  have h1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [h1]
  have h2 : 2 ^ n + 2 * 2 ^ n = 3 * 2 ^ n := by ring
  rw [h2]
  have : n ≥ 1 := by omega
  cases n with 
  | zero => 
    exfalso 
    exact Nat.lt_irrefl 0 h
  | succ n =>
    cases n with
    | zero =>
      norm_num -- Base case: n = 1
    | succ n =>
      norm_num
      <;> omega -- Inductive step: assuming true for n, prove for n + 1