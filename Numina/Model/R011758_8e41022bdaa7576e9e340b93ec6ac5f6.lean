import Mathlib

theorem number_theory_291954 : Set.ncard {(p, q) : ℕ×ℕ | p ≤ q ∧ q ≤ 100 ∧ p.Prime ∧ q.Prime ∧ |(p : ℤ) - q| = 2} = 8 := by
  have h1 : {(p, q) : ℕ×ℕ | p ≤ q ∧ q ≤ 100 ∧ p.Prime ∧ q.Prime ∧ |(p : ℤ) - q| = 2} = 
          Finset.filter (λ s : ℕ×ℕ =>
            s.1 ≤ s.2 ∧ s.2 ≤ 100 ∧ Nat.Prime s.1 ∧ Nat.Prime s.2 ∧ |(s.1 : ℤ) - s.2| = 2
          ) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨p, q⟩
    simp
    <;> aesop
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide