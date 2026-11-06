import Mathlib

open Nat

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_511 :
    Set.ncard {a | a ∈ Finset.Icc 100 999 ∧ S a = S (2 * a)} = 80 := by
  have : {a | a ∈ Finset.Icc 100 999 ∧ S a = S (2 * a)} = Finset.filter (fun a => S a = S (2 * a)) (Finset.Icc 100 999) := by
    ext a
    simp
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide