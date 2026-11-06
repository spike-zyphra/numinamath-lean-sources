import Mathlib

theorem number_theory_132415 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) :
    ((n + (10 * (n % 10) + (n / 10))) / (Nat.digits 10 n).sum)^2 = 121 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  interval_cases n <;> norm_num
  <;> all_goals native_decide