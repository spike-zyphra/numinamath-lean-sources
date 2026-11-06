import Mathlib

open Nat

theorem number_theory_4572'
    (n k : ℕ) (hpos : k > 0) (hle : k ≤ n) :
    Nat.choose n k + Nat.choose n (k - 1) = Nat.choose (n + 1) k := by
  cases k with
  | zero =>
    linarith
  | succ k =>
    simp [Nat.choose_succ_right, Nat.choose_succ_left, add_assoc, hle]
    <;> omega