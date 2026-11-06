import Mathlib

theorem number_theory_222325 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).sum = 11)
    (h₂ : (Nat.digits 10 n).headI = 2 * (Nat.digits 10 n).tail.tail.headI) (h₃ : n + 297 = (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)))) :
    n = 326 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> simp [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₁ h₂ h₃ ⊢
  <;> all_goals
    omega