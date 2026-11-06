import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_14826 : {k: ℝ | ∀ x : ℝ, (-5 * x ^ 2 + 2 * x + k) ≠ 0} = Set.Iio (-1 / 5) := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_Iio]
  constructor
  · -- Assume k ∈ {∀ x, -5x² + 2x + k ≠ 0}, prove k ∈ (-∞, -1/5)
    intro h
    by_contra h'
    push_neg at h'
    have h1 : k ≥ -1/5 := by linarith
    have h2 : ∃ x : ℝ, -5 * x ^ 2 + 2 * x + k = 0 := by 
      use (2 - Real.sqrt (4 + 20 * k)) / 10
      nlinarith [Real.sqrt_nonneg (4 + 20 * k), Real.sq_sqrt (show (0 : ℝ) ≤ 4 + 20 * k by 
        nlinarith
      )
    ]
    rcases h2 with ⟨x, hx⟩
    have h3 := h x
    contradiction
  · -- Assume k ∈ (-∞, -1/5), prove k ∈ {∀ x, -5x² + 2x + k ≠ 0}
    intro h x 
    by_contra h2
    have h2 : -5 * x ^ 2 + 2 * x + k = 0 := by 
      linarith
    have h3 : (4 + 20 * k : ℝ) < (0 : ℝ) := by
      nlinarith
    nlinarith [sq_nonneg (5 * x - 1), sq_nonneg (x - (2 / 10)), sq_nonneg (x - 0), sq_nonneg ((2 : ℝ)), sq_nonneg (4 : ℝ), sq_nonneg ( -2 - 10 * x), sq_nonneg (5 * x - 1)
    ]