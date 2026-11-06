import Mathlib

open Finset

theorem number_theory_166861 : (∑ n ∈ (Icc 2 50).filter (fun n => Nat.gcd n 50 = 1), (∏ x ∈ (Icc 1 n).filter (fun y => Nat.Coprime y n), x)) % 50 = 12 := by 
  native_decide