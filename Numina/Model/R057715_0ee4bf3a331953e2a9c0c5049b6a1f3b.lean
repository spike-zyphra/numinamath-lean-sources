import Mathlib

theorem number_theory_206956 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n = 12 * (Nat.digits 10 n).sum) :
    n = 108 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₂, h₃⟩
  interval_cases n <;> norm_num at h₁ <;> omega