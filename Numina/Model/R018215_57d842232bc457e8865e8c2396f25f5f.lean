import Mathlib

theorem algebra_15852 (n : ℕ) (h₀ : n ∈ Finset.range 10) (h₁ : 9 ∣ 24600 + 10 * n + 8) :
    n = 7 := by
  rw [Finset.mem_range] at h₀
  omega