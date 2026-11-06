import Mathlib

theorem number_theory_61006 :
    {n : ℕ | n ∈ Finset.Icc 1000000 9999999 ∧ (Nat.digits 10 n).all (fun d => d = 5 ∨ d = 7) ∧ 35 ∣ n}.ncard = 9 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000000 9999999 ∧ (Nat.digits 10 n).all (fun d => d = 5 ∨ d = 7) ∧ 35 ∣ n} = Finset.filter (fun n => (Nat.digits 10 n).all (fun d => d = 5 ∨ d = 7) ∧ 35 ∣ n) (Finset.Icc 1000000 9999999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide