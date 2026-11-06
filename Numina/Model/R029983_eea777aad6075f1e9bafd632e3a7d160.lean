import Mathlib

theorem negated_number_theory_74776 : Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 27 ∣ n ∧ 27 ∣ (Nat.digits 10 n).sum} = 75 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 27 ∣ n ∧ 27 ∣ (Nat.digits 10 n).sum} = Finset.filter (fun n => 27 ∣ n ∧ 27 ∣ (Nat.digits 10 n).sum) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide