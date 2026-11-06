import Mathlib

theorem number_theory_320719 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).all (fun d => d ≠ 0) ∧
      (Nat.digits 10 n).permutations.all (fun p => ¬(4 ∣ Nat.ofDigits 10 p))} = 283 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).all (fun d => d ≠ 0) ∧
      (Nat.digits 10 n).permutations.all (fun p => ¬(4 ∣ Nat.ofDigits 10 p))} = Finset.filter (fun n =>
      (Nat.digits 10 n).all (fun d => d ≠ 0) ∧ (Nat.digits 10 n).permutations.all (fun p => ¬(4 ∣ Nat.ofDigits 10 p))
      ) (Finset.Icc 100 999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide