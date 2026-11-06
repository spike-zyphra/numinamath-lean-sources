import Mathlib

theorem other_291889 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 1000 ∧ 4 ∣ n ∧ ¬(∃ k, k ∈ Nat.digits 10 n ∧ k = 4)} = 162 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 1000 ∧ 4 ∣ n ∧ ¬(∃ k, k ∈ Nat.digits 10 n ∧ k = 4)} = Finset.filter (fun n => 4 ∣ n ∧ ¬(∃ k, k ∈ Nat.digits 10 n ∧ k = 4)) (Finset.Icc 1 1000) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide