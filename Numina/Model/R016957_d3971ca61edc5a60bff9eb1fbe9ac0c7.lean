import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_197301 (p : ℝ) :
  (∀ x : ℝ, -9 < (3 * x ^ 2 + p * x - 6) / (x ^ 2 - x + 1) ∧ (3 * x ^ 2 + p * x - 6) / (x ^ 2 - x + 1) < 6) ↔
  p ∈ Ioo (-3) 6 := by
  constructor
  · -- Forward direction
    intro h
    have h2 := h 1
    rcases h2 with ⟨h21, h22⟩
    have h3 := h (-1)
    rcases h3 with ⟨h31, h32⟩
    have h4 := h 2
    rcases h4 with ⟨h41, h42⟩
    have h5 := h 3
    rcases h5 with ⟨h51, h52⟩
    constructor
    · -- Show -3 < p
      by_contra h6
      push_neg at h6
      have h7 : p ≤ -3 := by linarith
      have h8 := h (1 / 2)
      rcases h8 with ⟨h81, h82⟩
      norm_num at h81
      all_goals nlinarith
    · -- Show p < 6
      by_contra h8
      push_neg at h8
      have h9 : p ≥ 6 := by linarith
      have h10 := h 2
      rcases h10 with ⟨h101, h102⟩
      norm_num at h102
      all_goals nlinarith
  · -- Backward direction
    rintro ⟨hp1, hp2⟩
    intro x
    have hx2_pos : x ^ 2 - x + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    constructor
    · -- Show -9 < (3 * x ^ 2 + p * x - 6) / (x ^ 2 - x + 1)
      apply (lt_div_iff₀ hx2_pos).mpr
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - (p + 6) / 6), sq_nonneg (x + 3), sq_nonneg (x - 21 / 2), sq_nonneg (x * (x - 1)), sq_nonneg ((p + 3) * (x - 1 / 2)), sq_nonneg ((6 - p) * (x - 2)), sq_nonneg (p * x)]
    · -- Show (3 * x ^ 2 + p * x - 6) / (x ^ 2 - x + 1) < 6
      apply (div_lt_iff₀ hx2_pos).mpr
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - (p + 6) / 6), sq_nonneg (x + 24 / 2), sq_nonneg (x - 21 / 2), sq_nonneg (x * (x - 1 / 2)), sq_nonneg ((p - 9) * (x - 1 / 2)), sq_nonneg ((6 - p) * (x - 2)), sq_nonneg (p * x)]