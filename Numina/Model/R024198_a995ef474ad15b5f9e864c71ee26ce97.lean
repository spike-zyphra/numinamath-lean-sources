import Mathlib

theorem algebra_236748 (x : ℕ → ℝ)
    (h₀ : ∑ i ∈ Finset.range 30, (20 + i)^3 * x i = 13)
    (h₁ : ∑ i ∈ Finset.range 30, (21 + i)^3 * x i = 1)
    (h₂ : ∑ i ∈ Finset.range 30, (22 + i)^3 * x i = 19) :
    ∑ i ∈ Finset.range 30, (21 + i) * x i = 5 := by
  have eq1 : ∑ i ∈ Finset.range 30, (21 + i) * x i = 
    (1/6) * (∑ i ∈ Finset.range 30, (20 + i)^3 * x i) - (1/3) * (∑ i ∈ Finset.range 30, (21 + i)^3 * x i) + (1/6) * (∑ i ∈ Finset.range 30, (22 + i)^3 * x i) := by 
    simp [Finset.sum_range_succ]
    ring_nf
  rw [eq1, h₀, h₁, h₂]
  norm_num