import Mathlib

theorem number_theory_2944 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).all (fun d => d ≠ 6) ∧ 12 ∣ n} = 45 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).all (fun d => d ≠ 6) ∧ 12 ∣ n} = Finset.filter (fun n => (Nat.digits 10 n).all (fun d => d ≠ 6) ∧ 12 ∣ n) (Finset.Icc 100 999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide