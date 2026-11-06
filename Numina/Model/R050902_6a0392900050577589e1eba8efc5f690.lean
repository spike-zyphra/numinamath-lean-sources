import Mathlib

theorem number_theory_183730 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).length = 3)
    (h₂ : (Nat.digits 10 n)[1]! = 6) (h₃ : (Nat.digits 10 n).sum = 10) :
    n = 163 ∨ n = 361 ∨ n = 262 ∨ n = 460 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢ <;> omega