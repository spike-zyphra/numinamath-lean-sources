import Mathlib

theorem number_theory_287118 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 = 150 ∧ 3 ∣ p.1 ∧ 5 ∣ p.2} = 9 := by
  have h1 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 = 150 ∧ 3 ∣ p.1 ∧ 5 ∣ p.2} = Finset.filter (fun p => p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 = 150 ∧ 3 ∣ p.1 ∧ 5 ∣ p.2) (Finset.Icc (0 : ℕ) 150 ×ˢ Finset.Icc (0 : ℕ) 150) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide