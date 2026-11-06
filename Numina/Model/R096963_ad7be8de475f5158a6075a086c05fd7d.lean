import Mathlib

theorem number_theory_184990 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 2000 ∧ Nat.Coprime x 2001} = 1232 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 2000 ∧ Nat.Coprime x 2001} = Finset.filter (fun x => Nat.Coprime x 2001) (Finset.Icc 1 2000) := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide