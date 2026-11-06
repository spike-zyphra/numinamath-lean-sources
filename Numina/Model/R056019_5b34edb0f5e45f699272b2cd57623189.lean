import Mathlib

theorem algebra_259588 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : n = 2 * (Nat.digits 10 n).prod) :
    n = 36 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁₀, h₁₁⟩
  interval_cases n <;> norm_num at h₁ ⊢ <;> all_goals omega