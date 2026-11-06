import Mathlib

theorem number_theory_186405 : {n : ℕ | n ∈ Finset.Icc 1 1997 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 5]}.ncard = 399 := by
  have : {n : ℕ | n ∈ Finset.Icc 1 1997 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 5]} = Finset.filter (fun n => (Nat.digits 10 n).sum ≡ 0 [MOD 5]) (Finset.Icc 1 1997) := by
    ext n
    simp
    <;> tauto
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide