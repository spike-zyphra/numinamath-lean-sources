import Mathlib

theorem number_theory_316053 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), d ∈ Finset.Icc 1 4 ∧
      11 ∣ n} = 8 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
    (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), d ∈ Finset.Icc 1 4 ∧
    11 ∣ n} = Finset.filter (fun n => 
      (Nat.digits 10 n).length = 4 ∧
        (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), d ∈ Finset.Icc 1 4 ∧
        11 ∣ n) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide