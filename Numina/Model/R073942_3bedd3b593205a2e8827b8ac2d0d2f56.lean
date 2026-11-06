import Mathlib

theorem number_theory_288242 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).length = 3)
    (h₂ : (Nat.digits 10 n).headI = 2) (h₃ : (Nat.digits 10 n).tail.headI = 1) (h₄ : (Nat.digits 10 n).tail.tail.headI = 2) :
    n = 212 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ h₄ ⊢ <;> all_goals native_decide