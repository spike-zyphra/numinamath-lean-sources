import Mathlib

theorem number_theory_244360 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ ∃ k, (Nat.digits 10 n).get k = 3 ∧ 3 ∣ n} = 12504 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ ∃ k, (Nat.digits 10 n).get k = 3 ∧ 3 ∣ n} = Finset.filter (fun n => 3 ∣ n ∧ ∃ k, (Nat.digits 10 n).get k = 3) (Finset.Icc 10000 99999) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide