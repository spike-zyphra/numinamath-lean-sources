import Mathlib

theorem number_theory_324481 :
    Set.ncard {x : ℕ | x > 0 ∧ x ≤ 1000 ∧ (Nat.digits 10 x).sum ≡ 1 [MOD 2] ∧ (Nat.digits 10 (x + 1)).sum ≡ 1 [MOD 2]} = 46 := by
  have h1 : {x : ℕ | x > 0 ∧ x ≤ 1000 ∧ (Nat.digits 10 x).sum ≡ 1 [MOD 2] ∧ (Nat.digits 10 (x + 1)).sum ≡ 1 [MOD 2]} = Finset.filter (fun x => x > 0 ∧ x ≤ 1000 ∧ (Nat.digits 10 x).sum ≡ 1 [MOD 2] ∧ (Nat.digits 10 (x + 1)).sum ≡ 1 [MOD 2]) (Finset.Icc 0 1000) := by 
    ext x 
    simp 
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide
  <;> try { tauto }