import Mathlib

theorem number_theory_258113 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).sum = 24) :
    (n = 888 ∨ n = 699 ∨ n = 969 ∨ n = 996 ∨ n = 789 ∨ n = 798 ∨ n = 879 ∨ n = 897 ∨ n = 978 ∨ n = 987) := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h100, h999⟩
  interval_cases n <;> norm_num at h₁ <;> omega