import Mathlib

theorem number_theory_182783 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ n % 11 = 0 ∧ (Nat.digits 10 n).sum ≡ 0 [ZMOD 11]} = 72 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ n % 11 = 0 ∧ (Nat.digits 10 n).sum ≡ 0 [ZMOD 11]} = Finset.filter (fun n => n % 11 = 0 ∧ (Nat.digits 10 n).sum ≡ 0 [ZMOD 11]) (Finset.Icc 1000 9999) := by
    ext n 
    simp
    <;> try { tauto }
    <;> try { norm_num }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide