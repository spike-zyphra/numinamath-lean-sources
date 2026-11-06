import Mathlib

theorem algebra_256616 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 ≤ 100 ∧ (p.1 + 1 / p.2 : ℚ) / (1 / p.1 + p.2) = 13} = 7 := by
  have h1 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 ≤ 100 ∧ (p.1 + 1 / p.2 : ℚ) / (1 / p.1 + p.2) = 13} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 ≤ 100 ∧ (p.1 + 1 / p.2 : ℚ) / (1 / p.1 + p.2) = 13) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide