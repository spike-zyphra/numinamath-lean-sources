import Mathlib

theorem number_theory_119957 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 99 ∧ (2 ∣ n ∨ 2 ∈ Nat.digits 10 n ∨ 2 ∣ (Nat.digits 10 n).sum)} = 79 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 99 ∧ (2 ∣ n ∨ 2 ∈ Nat.digits 10 n ∨ 2 ∣ (Nat.digits 10 n).sum)} = Finset.filter (fun (x : ℕ) => 2 ∣ x ∨ 2 ∈ Nat.digits 10 x ∨ 2 ∣ (Nat.digits 10 x).sum) (Finset.Icc 1 99) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide