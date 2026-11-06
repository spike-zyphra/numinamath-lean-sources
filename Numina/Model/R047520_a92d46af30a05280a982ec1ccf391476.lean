import Mathlib

open Set Real

theorem inequalities_172451 {k : ℝ} (hk : k ≠ 0) :
    {x | k * x ^ 2 - 2 * x + 6 * k < 0} ⊆ Ioo 2 3 ↔ k ≥ 2 / 5 := by

  constructor
  · -- Assume {x | k * x ^ 2 - 2 * x + 6 * k < 0} ⊆ Ioo 2 3, prove k ≥ 2 / 5
    intro h
    by_contra h1
    push_neg at h1
    have h2 : (2 : ℝ) ∈ {x | k * x ^ 2 - 2 * x + 6 * k < 0} := by
      simp
      nlinarith
    have h3 : (2 : ℝ) ∈ Ioo (2 : ℝ) 3 := by
      apply h
      exact h2
    norm_num at h3
  · -- Assume k ≥ 2 / 5, prove {x | k * x ^ 2 - 2 * x + 6 * k < 0} ⊆ Ioo 2 3
    intro hk1
    intro x hx
    have h1 : k * x ^ 2 - 2 * x + 6 * k < 0 := by 
      simpa using hx
    have h2 : 2 < x := by 
      by_contra h2
      push_neg at h2
      nlinarith [sq_nonneg (x - 2), sq_nonneg (k * (x) - 1),
          sq_nonneg (k * (x) - 2), sq_nonneg (k * (3 - x)), sq_nonneg ((2 - x) * k), 
          sq_pos_of_ne_zero (show k ≠ 0 by exact_mod_cast hk)
        ]
    have h3 : x < 3 := by 
      by_contra h3
      push_neg at h3
      nlinarith [sq_nonneg (x - 3), sq_nonneg (k * (x) - 1),
          sq_nonneg (k * (x) - 2), sq_nonneg (k * (2 - x)), sq_nonneg ((x - 3) * k),
          sq_pos_of_ne_zero (show k ≠ 0 by exact_mod_cast hk)
        ]
    exact ⟨h2, h3⟩