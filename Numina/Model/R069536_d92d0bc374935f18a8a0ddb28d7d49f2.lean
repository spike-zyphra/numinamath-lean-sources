import Mathlib

theorem algebra_52557 (x : Fin 7 → ℝ)
    (h1 : ∑ i ∈ Finset.range 7, (i + 1)^2 * x i = 1)
    (h2 : ∑ i ∈ Finset.range 7, (i + 1)^2 * 4 * x i = 12)
    (h3 : ∑ i ∈ Finset.range 7, (i + 1)^2 * 9 * x i = 123) :
    ∑ i ∈ Finset.range 7, (i + 1)^2 * 16 * x i = 334 := by
  simp [Finset.sum_range_succ] at h1 h2 h3 ⊢
  linarith