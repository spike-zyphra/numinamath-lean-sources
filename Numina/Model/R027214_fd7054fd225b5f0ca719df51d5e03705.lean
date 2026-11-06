import Mathlib

theorem number_theory_175574 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ 3 ∈ (Nat.digits 10 n) ∧
        4 ∈ (Nat.digits 10 n) ∧ 6 ∈ (Nat.digits 10 n) ∧ 7 ∈ (Nat.digits 10 n) ∧
        44 ∣ n} = 2 := by
  have : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ 3 ∈ (Nat.digits 10 n) ∧
        4 ∈ (Nat.digits 10 n) ∧ 6 ∈ (Nat.digits 10 n) ∧ 7 ∈ (Nat.digits 10 n) ∧
        44 ∣ n} = Finset.filter (fun n => (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ 3 ∈ (Nat.digits 10 n) ∧
        4 ∈ (Nat.digits 10 n) ∧ 6 ∈ (Nat.digits 10 n) ∧ 7 ∈ (Nat.digits 10 n) ∧
          44 ∣ n) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide