import Mathlib

theorem algebra_187473 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).sum = 18)
    (h₂ : (Nat.digits 10 n).length = 3) (h₃ : (Nat.digits 10 n)[2]! = (Nat.digits 10 n)[1]! + 1)
    (h₄ : (Nat.digits 10 n)[0]! = (Nat.digits 10 n)[1]! + 2) :
    n = 657 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₅, h₆⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ h₄ <;> all_goals
    omega