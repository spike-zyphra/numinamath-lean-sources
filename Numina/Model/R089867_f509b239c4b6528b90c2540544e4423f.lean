import Mathlib

theorem number_theory_251844 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 + Nat.gcd p.1 p.2 = 33} = 21 := by
  have h1 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 + Nat.gcd p.1 p.2 = 33} = Finset.filter (fun p => p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 + Nat.gcd p.1 p.2 = 33) (Finset.Icc (0 : ℕ) 50 ×ˢ Finset.Icc (0 : ℕ) 50) := by
    ext ⟨a, b⟩
    simp [Finset.mem_Icc]
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide