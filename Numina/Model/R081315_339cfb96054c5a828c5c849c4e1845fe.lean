import Mathlib

theorem number_theory_182674 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    n / (Nat.digits 10 n).sum ≤ 100 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h100, h999⟩
  interval_cases n <;> norm_num
  <;> all_goals 
    omega