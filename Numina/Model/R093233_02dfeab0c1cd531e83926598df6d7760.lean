import Mathlib

theorem number_theory_288083 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : 3 ∣ (Nat.digits 10 n).sum)
    (h₂ : (Nat.ofDigits 10 ((Nat.digits 10 n).reverse) ∈ Finset.Icc 10 99) ∧ n - 27 = Nat.ofDigits 10 ((Nat.digits 10 n).reverse)) :
    n = 96 ∨ n = 63 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₂ with ⟨h₅, h₆⟩
  interval_cases n <;> simp [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₁ h₅ h₆ <;> norm_num at h₁ h₅ h₆ <;> omega