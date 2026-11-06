import Mathlib

theorem number_theory_236059 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n - (Nat.digits 10 n).sum = 261) :
    (Nat.digits 10 n)[1]! = 7 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₂, h₃⟩
  interval_cases n <;> norm_num at h₁ ⊢ <;> simp_all <;> trivial