import Mathlib

theorem number_theory_199752 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (∀ d ∈ Nat.digits 10 n, Even d) ∧
      4 ∣ n ∧ ¬(4 ∣ (n / 10))} = 120 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (∀ d ∈ Nat.digits 10 n, Even d) ∧
    4 ∣ n ∧ ¬(4 ∣ (n / 10))} = Finset.filter (fun n => (∀ d ∈ Nat.digits 10 n, Even d) ∧ 4 ∣ n ∧ ¬(4 ∣ (n / 10))) (Finset.Icc 1000 9999) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide