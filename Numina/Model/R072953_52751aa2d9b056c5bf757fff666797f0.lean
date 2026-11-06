import Mathlib

theorem number_theory_148159 (N : ℕ) (h₀ : N ∈ Finset.Icc 100 999) (h₁ : 11 ∣ N)
    (h₂ : N / 11 = (Nat.digits 10 N).headI ^ 2 + (Nat.digits 10 N).tail.headI ^ 2 + (Nat.digits 10 N).tail.tail.headI ^ 2) :
    N = 550 ∨ N = 803 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases N <;> norm_num at h₁ h₂ ⊢ <;> tauto