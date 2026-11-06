import Mathlib

open Finset

def φ! (n : ℕ) : ℕ :=
    ∏ x ∈ {x ∈ Icc 1 n | Nat.Coprime x n}, x

theorem number_theory_609535 :
    (∑ n ∈ {n ∈ Icc 2 50 | Nat.gcd n 50 = 1}, φ! n) % 50 = 12 := by 
  have h1 : {n ∈ Icc 2 50 | Nat.gcd n 50 = 1} = 
    (Icc 2 50).filter (fun n => Nat.gcd n 50 = 1) := by
    ext n
    simp 
  rw [h1]
  native_decide