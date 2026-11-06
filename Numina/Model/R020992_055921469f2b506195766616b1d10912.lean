import Mathlib

theorem number_theory_106536 : ¬ (∀ n, ∃ p, Nat.Prime p ∧ p ∈ Finset.Icc n (n + 6)) := by
  intro h 
  have h90 := h 90
  rcases h90 with ⟨p, hp, hp2⟩
  rw [Finset.mem_Icc] at hp2
  have h1 : 90 ≤ p := by
    omega
  have h2 : p ≤ 96 := by
    omega
  interval_cases p <;> norm_num at hp ⊢ <;> omega