import Mathlib

theorem number_theory_234237 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ (Nat.digits 10 n).sum = 6 ∧ 11 ∣ n} = 6 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
    (Nat.digits 10 n).toFinset.card = 4 ∧ (Nat.digits 10 n).sum = 6 ∧ 11 ∣ n} = Finset.filter 
      (λ n => (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n).toFinset.card = 4 ∧ (Nat.digits 10 n).sum = 6 ∧ 11 ∣ n)
      (Finset.Icc 1000 9999) := by
      ext n
      simp
      <;> try omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide