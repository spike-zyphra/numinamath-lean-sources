import Mathlib

theorem number_theory_69458 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).all (fun d => d ≠ 0) ∧ 4 ∣ n ∧ ¬(8 ∣ n)} = 729 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).all (fun d => d ≠ 0) ∧ 4 ∣ n ∧ ¬(8 ∣ n)} = Finset.filter (fun n => (Nat.digits 10 n).all (fun d => d ≠ 0) ∧ 4 ∣ n ∧ ¬(8 ∣ n)) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide