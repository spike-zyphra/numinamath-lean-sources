import Mathlib

def is_coincidence_number (n : ℕ) : Prop :=
  (Nat.digits 10 n).sum = (Nat.digits 10 n).prod

theorem number_theory_106708 :
    Set.ncard {n | n ∈ Finset.Icc 10000 99999 ∧ is_coincidence_number n} = 40 := by
  have h1 : {n | n ∈ Finset.Icc 10000 99999 ∧ is_coincidence_number n} = Finset.filter (fun x => (Nat.digits 10 x).sum = (Nat.digits 10 x).prod) (Finset.Icc 10000 99999) := by
    ext n
    simp [is_coincidence_number]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide