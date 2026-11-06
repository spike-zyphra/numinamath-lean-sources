import Mathlib

theorem number_theory_214266 :
    Set.ncard {p : ℕ × ℕ | p.1^2 + p.2^2 + p.1 * p.2 ≡ 0 [MOD 9] ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 100} = 528 := by 
  have h1 : {p : ℕ × ℕ | p.1^2 + p.2^2 + p.1 * p.2 ≡ 0 [MOD 9] ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 100} = Finset.filter (fun p => (p.1^2 + p.2^2 + p.1 * p.2 ≡ 0 [MOD 9] ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 100)) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨a, b⟩
    simp [Nat.ModEq]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide