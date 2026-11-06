import Mathlib

def isVain (n : ℕ) := (Nat.digits 10 n).sum ≥ (Nat.digits 10 n).prod

theorem number_theory_174438 :
    Set.ncard {n | n ∈ Finset.Icc 10 99 ∧ isVain n} = 27 := by
  have h1 : {n | n ∈ Finset.Icc 10 99 ∧ isVain n} = Finset.filter (fun n => (Nat.digits 10 n).sum ≥ (Nat.digits 10 n).prod) (Finset.Icc 10 99) := by
    ext n
    simp [isVain]
    <;> try { aesop }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide