import Mathlib

theorem number_theory_115048 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n = (Nat.digits 10 n).headI ^ 3) :
    n = 125 ∨ n = 216 ∨ n = 729 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₂, h₃⟩
  interval_cases n <;> norm_num at h₁ ⊢ <;> omega