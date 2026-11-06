import Mathlib

theorem number_theory_276827 (n : ℕ) (h₀ : n % 7 = 0) (h₁ : n ∈ Finset.Icc 100 999)
    (h₂ : ∃ k, n % 100 = k * 11) :
    7 ∣ (Nat.digits 10 n).sum := by
  rw [Finset.mem_Icc] at h₁
  rcases h₁ with ⟨h₃, h₄⟩
  rcases h₂ with ⟨k, hk⟩
  interval_cases n <;> norm_num at h₀ hk h₃ h₄ ⊢
    <;> norm_num [Nat.digits, Nat.digitsAux] at *
    <;> omega