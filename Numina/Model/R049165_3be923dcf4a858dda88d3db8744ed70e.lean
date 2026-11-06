import Mathlib

theorem number_theory_154187 :
    Set.ncard {n : ℕ | n < 1998 ∧ Nat.Coprime n 1547} = 1487 := by
  have h1 : {n : ℕ | n < 1998 ∧ Nat.Coprime n 1547} = Finset.filter (fun n => n < 1998 ∧ Nat.Coprime n 1547) (Finset.Icc 0 1997) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide