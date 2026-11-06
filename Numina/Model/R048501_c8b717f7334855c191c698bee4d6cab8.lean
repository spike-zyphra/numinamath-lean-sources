import Mathlib

theorem number_theory_287209 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 2009 ∧ (Nat.digits 10 n).sum = 11} = 133 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 2009 ∧ (Nat.digits 10 n).sum = 11} = Finset.filter (fun n => (Nat.digits 10 n).sum = 11) (Finset.Icc 1 2009) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide