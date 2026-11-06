import Mathlib

theorem algebra_175928 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (Nat.digits 10 n).sum = 12)
    (h₂ : n - (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = 54) :
    n = 93 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₁ h₂ ⊢ <;> all_goals omega