import Mathlib

open Finset

theorem number_theory_4441 : {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 0 [MOD 3]}.ncard = 1691 ∧
    {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 1 [MOD 3]}.ncard = 164 ∧
    {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 2 [MOD 3]}.ncard = 160 := by
  have h1 : {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 0 [MOD 3]}.ncard = 1691 := by
    have : {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 0 [MOD 3]} = Finset.filter (fun i => (Nat.choose 2014 i) ≡ 0 [MOD 3]) (Finset.Iic 2014) := by
      ext i
      simp
      <;> tauto
    rw [this]
    rw [Finset.filter]
    simp [Finset.Iic]
    <;> try { native_decide }
  have h2 : {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 1 [MOD 3]}.ncard = 164 := by
    have : {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 1 [MOD 3]} = Finset.filter (fun i => (Nat.choose 2014 i) ≡ 1 [MOD 3]) (Finset.Iic 2014) := by
      ext i
      simp
      <;> tauto
    rw [this]
    rw [Finset.filter]
    simp [Finset.Iic]
    <;> try { native_decide }
  have h3 : {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 2 [MOD 3]}.ncard = 160 := by
    have : {i : ℕ | i ≤ 2014 ∧ (Nat.choose 2014 i) ≡ 2 [MOD 3]} = Finset.filter (fun i => (Nat.choose 2014 i) ≡ 2 [MOD 3]) (Finset.Iic 2014) := by
      ext i
      simp
      <;> tauto
    rw [this]
    rw [Finset.filter]
    simp [Finset.Iic]
    <;> try { native_decide }
  exact ⟨h1, h2, h3⟩