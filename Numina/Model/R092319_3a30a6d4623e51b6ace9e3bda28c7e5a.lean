import Mathlib

theorem number_theory_315093 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n = 29 * (Nat.digits 10 n).sum) :
    n = 261 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀1, h₀2⟩
  interval_cases n <;> norm_num at h₁ ⊢ <;> all_goals try { trivial }
  <;> omega