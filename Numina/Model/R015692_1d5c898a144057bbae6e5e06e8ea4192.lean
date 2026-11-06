import Mathlib

theorem number_theory_55951 : {n : ℕ | 1 ≤ n ∧ n ≤ 455 ∧ n ^ 3 ≡ 1 [MOD 455]}.encard = 9 := by 
  have : {n : ℕ | 1 ≤ n ∧ n ≤ 455 ∧ n ^ 3 ≡ 1 [MOD 455]} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 455 ∧ n ^ 3 ≡ 1 [MOD 455]) (Finset.Icc 0 455) := by 
    ext n 
    simp [Nat.ModEq]
    <;> try { tauto }
  rw [this] 
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide