import Mathlib

theorem number_theory_242098 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 11 ∣ n)
    (h₂ : (Nat.digits 10 n).sum = 10) :
    n = 154 ∨ n = 253 ∨ n = 352 ∨ n = 451 ∨ n = 550 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num at h₁ h₂ ⊢ <;> omega