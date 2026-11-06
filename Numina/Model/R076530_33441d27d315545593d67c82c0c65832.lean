import Mathlib

theorem algebra_60868 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 < 1000 ∧ p.2 < 1000 ∧ p.1 * p.2 = (p.2 ^ 2) / p.1} = 31 := by
  have h1 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 < 1000 ∧ p.2 < 1000 ∧ p.1 * p.2 = (p.2 ^ 2) / p.1} = Finset.filter (fun s => (s.1 > 0 ∧ s.2 > 0 ∧ s.1 < 1000 ∧ s.2 < 1000 ∧ s.1 * s.2 = (s.2 ^ 2) / s.1)) (Finset.Icc (0 : ℕ) 999 ×ˢ Finset.Icc (0 : ℕ) 999) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide