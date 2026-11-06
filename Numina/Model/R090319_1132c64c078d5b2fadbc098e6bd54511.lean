import Mathlib

theorem number_theory_287360 :
    Set.ncard {p : ℕ × ℕ | p.1 * p.2 ≡ 0 [MOD 33] ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 40} = 64 := by
  have h1 : {p : ℕ × ℕ | p.1 * p.2 ≡ 0 [MOD 33] ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 40} = Finset.filter (fun p => p.1 * p.2 ≡ 0 [MOD 33] ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 40) (Finset.Icc (0 : ℕ) 40 ×ˢ Finset.Icc (0 : ℕ) 40) := by
    ext ⟨m, n⟩
    simp [Nat.ModEq]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide