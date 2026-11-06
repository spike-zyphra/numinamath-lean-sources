import Mathlib

theorem number_theory_226544 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) :
    n = 2 * (Nat.digits 10 n).prod ↔ n = 36 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁₀, h₂₀⟩
  constructor
  · -- Assume n = 2 * (Nat.digits 10 n).prod, prove n = 36
    intro h
    interval_cases n <;> norm_num at h ⊢ <;> all_goals
      native_decide
  · -- Assume n = 36, prove n = 2 * (Nat.digits 10 n).prod
    intro h
    rw [h]
    all_goals native_decide