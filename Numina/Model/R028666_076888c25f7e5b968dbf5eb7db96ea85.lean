import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_325105 (t : ℝ) :
  (∃ x : ℝ, x ∈ Icc (-1) 1 ∧ (arccos x)^2 + (2 - t) * arccos x + 4 = 0) ↔ t ≥ 6 := by
  constructor
  -- Proof of the forward direction
  · -- Assume there exists x such that x is in [-1,1] and (arccos x)² + (2-t)(arccos x) + 4 = 0
    intro h
    rcases h with ⟨x, hx1, hx2⟩
    have h1 : -1 ≤ x ∧ x ≤ 1 := by
      simpa using hx1
    have h2 : 0 ≤ arccos x := by
      apply arccos_nonneg
    have h3 : arccos x ≤ Real.pi := by
      apply arccos_le_pi
    by_contra h
    push_neg at h
    by_cases h4 : arccos x = (0 : ℝ)
    · -- Substitute arccos x = 0 into hx2
      rw [h4] at hx2
      nlinarith [Real.pi_gt_three]
    · -- Case arccos x ≠ 0
      have h4' : arccos x ≠ 0 := h4
      have hx5 : (arccos x) ^ 2 + (2 - t) * (arccos x) + 4 = 0 := by 
        linarith [hx2]
      nlinarith [sq_nonneg (arccos x - 2), Real.pi_gt_three, 
        Real.pi_pos, sq_nonneg (t - 6), mul_pos (show 0 < Real.pi - 3 by nlinarith [Real.pi_gt_three]) (show 0 < Real.pi - 3 by nlinarith [Real.pi_gt_three]), 
        sq_nonneg (arccos x), sq_nonneg (arccos x ^ 2), 
        h4'
      ]
  · -- Proof of the reverse direction
    intro ht
    have h1 : t ≥ 6 := ht
    have h2 : (t - 2 : ℝ) ^ 2 ≥ 16 := by
      nlinarith
    have h3 : t - 2 ≥ 4 := by nlinarith
    set y := ((t - 2) - Real.sqrt ((t - 2) ^ 2 - 16)) / 2 with hy
    have hy1 : y ≥ 0 := by
      nlinarith [Real.sqrt_nonneg ((t - 2) ^ 2 - 16), Real.sq_sqrt (show (0 : ℝ) ≤ (t - 2) ^ 2 - 16 by nlinarith), h2, h3]
    have hy2 : y ≤ Real.pi := by
      nlinarith [Real.sqrt_nonneg ((t - 2) ^ 2 - 16), Real.sq_sqrt (show (0 : ℝ) ≤ (t - 2) ^ 2 - 16 by nlinarith), Real.pi_gt_three, Real.pi_pos, sq_nonneg ( ( (t - 2 : ℝ ) - Real.sqrt ((t - 2) ^ 2 - 16) - 2 * Real.pi ) ), sq_nonneg ( (t - 2 : ℝ) - 2 * Real.pi ) ]
    set x := Real.cos y with hx
    have hx1 : x ∈ Icc (-1 : ℝ) 1 := by
      have h4 : -1 ≤ Real.cos y ∧ Real.cos y ≤ 1 := Real.cos_mem_Icc y
      constructor
      · -- Show x ≥ -1
        nlinarith [h4.1]
      · -- Show x ≤ 1
        nlinarith [h4.2]
    have hx5 : arccos x = y := by
      rw [show x = Real.cos y by linarith [hx]]
      apply arccos_cos
      all_goals
      nlinarith [hy1, hy2]
    have hx2 : (arccos x) ^ 2 + (2 - t) * (arccos x) + 4 = 0 := by
      rw [show arccos x = y by linarith [hx5]]
      nlinarith [Real.sqrt_nonneg ((t - 2 : ℝ) ^ 2 - 16), Real.sq_sqrt (show (0 : ℝ) ≤ (t - 2 : ℝ) ^ 2 - 16 by nlinarith), sq_nonneg ((t - 2 : ℝ) - Real.sqrt ((t - 2 : ℝ) ^ 2 - 16)), sq_nonneg ((t - 2 : ℝ) ^ 2 - 16), sq_nonneg (y ^ 2), Real.pi_gt_three, Real.pi_pos, h3]
    exact ⟨x, hx1, hx2⟩