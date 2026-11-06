import Mathlib

def isFriendly (n : ℕ) : Prop :=
  n % (Nat.digits 10 n).sum = 0

theorem number_theory_100989 :
    Set.ncard {n | n ∈ Finset.Icc 10 99 ∧ isFriendly n} = 23 := by
  have h : {n | n ∈ Finset.Icc 10 99 ∧ isFriendly n} = Finset.filter (fun (n : ℕ) => n % (Nat.digits 10 n).sum = 0) (Finset.Icc 10 99) := by
    ext n
    simp [isFriendly]
    <;> tauto
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide