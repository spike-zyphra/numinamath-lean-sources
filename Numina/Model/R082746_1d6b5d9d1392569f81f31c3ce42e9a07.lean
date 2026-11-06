import Mathlib

theorem algebra_1408 (n S T : ℕ) (h₀ : S = ∑ i ∈ Finset.range 10, (n + i)) (h₁ : T = 10 * n) : S - T = 45 := by
  have h2 : S = 10 * n + 45 := by
    rw [h₀]
    -- Compute the sum explicitly
    norm_num [Finset.sum_range_succ]
    <;> ring_nf <;> omega
  calc 
    S - T = (10 * n + 45) - (10 * n) := by rw [h2, h₁]
    _ = 45 := by omega