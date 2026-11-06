import Mathlib

theorem number_theory_245543 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : Nat.digits 7 n = [a, b, c])
    (h₂ : Nat.ofDigits 9 [c, b, a] = n) :
    n = 248 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> simp [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₁ h₂ ⊢
  <;> omega