import Mathlib

theorem number_theory_242132 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : ∃ k, n % 100 = k * 11) :
    7 ∣ n → 7 ∣ (Nat.digits 10 n).sum := by 
  intro h2
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨k, hk⟩
  interval_cases n <;> norm_num at *
  <;> norm_num [Nat.digits, Nat.digitsAux] at *
  <;> omega