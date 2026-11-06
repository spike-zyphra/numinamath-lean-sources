import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_140440 : IsLeast {x | ∃ t : ℝ, x = cos (3*t) + 4 * cos (2*t) + 8 * cos t} (-5) := by
  constructor
  · -- Show -5 is in the set.
    use Real.pi
    have h1 : cos (3 * Real.pi) = -1 := by
      have h1 : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
      rw [h1]
      have h2 : cos (Real.pi + 2 * Real.pi) = cos (Real.pi) := by
        rw [cos_add_two_pi]
      have h3 : cos (Real.pi) = -1 := Real.cos_pi
      rw [h2, h3]
    have h2 : cos (2 * Real.pi) = 1 := by 
      exact Real.cos_two_pi
    have h3 : cos Real.pi = -1 := Real.cos_pi
    rw [h1, h2, h3]
    norm_num
  · -- Show that -5 is minimal
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : cos (3 * t) = 4 * cos t ^ 3 - 3 * cos t := by 
      rw [cos_three_mul]
    have h2 : cos (2 * t) = 2 * cos t ^ 2 - 1 := by 
      rw [cos_two_mul]
    have h3 : cos (3 * t) + 4 * cos (2 * t) + 8 * cos t = 4 * cos t ^ 3 + 8 * cos t ^ 2 + 5 * cos t - 4 := by
      rw [h1, h2]
      ring_nf
    have h4 : 4 * cos t ^ 3 + 8 * cos t ^ 2 + 5 * cos t - 4 ≥ -5 := by 
      have hcos : -1 ≤ cos t ∧ cos t ≤ 1 := by 
        constructor
        · linarith [neg_one_le_cos t, cos_le_one t]
        · linarith [neg_one_le_cos t, cos_le_one t]
      nlinarith [sq_nonneg (cos t + 1), sq_nonneg (2 * cos t + 1), sq_nonneg (cos t - (-1)), sq_nonneg (cos t), Real.cos_le_one t, Real.neg_one_le_cos t]
    have h5 : cos (3 * t) + 4 * cos (2 * t) + 8 * cos t ≥ -5 := by 
      nlinarith [h3, h4]
    nlinarith [ht, h5]