import Mathlib

theorem number_theory_213151 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 8 n).length = 3)
    (h₂ : (Nat.digits 10 n).sum = 14) (h₃ : (Nat.digits 8 n).sum = 14) :
    n = 455 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢ <;> all_goals
    omega