import Mathlib

theorem algebra_178164 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (Nat.digits 10 n).sum = 12)
    (h₂ : n + 36 = (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)))) :
    n = 48 := by 
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₃, h₄⟩ 
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₁ h₂ ⊢ 
  <;> omega