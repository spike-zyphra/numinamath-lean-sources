import Mathlib

theorem number_theory_95495 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 5 ∣ n ∧ (n / 10000) % 10 = n % 10 ∧ (Nat.digits 10 n).sum ≡ 0 [ZMOD 5]} = 200 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 5 ∣ n ∧ (n / 10000) % 10 = n % 10 ∧ (Nat.digits 10 n).sum ≡ 0 [ZMOD 5]} = Finset.filter (fun n => 5 ∣ n ∧ (n / 10000) % 10 = n % 10 ∧ (Nat.digits 10 n).sum ≡ 0 [ZMOD 5]) (Finset.Icc 10000 99999) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide