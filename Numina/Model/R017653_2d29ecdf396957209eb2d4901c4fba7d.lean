import Mathlib

theorem number_theory_227824 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : Nat.digits 10 (91 * n) = List.reverse (Nat.digits 10 (91 * n))) (h₂ : Nat.digits 10 (93 * n) = List.reverse (Nat.digits 10 (93 * n))) (h₃ : Nat.digits 10 (95 * n) = List.reverse (Nat.digits 10 (95 * n))) (h₄ : Nat.digits 10 (97 * n) = List.reverse (Nat.digits 10 (97 * n))) :
    n = 55 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₅, h₆⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ h₄ ⊢ <;> all_goals 
    try { trivial }