import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_159247 :
  IsLeast {y : ℝ | ∃ x ∈ Ioo 0 Real.pi, y = (25 * x ^ 2 * (sin x) ^ 2 + 16) / (x * sin x)} 40 := by
  constructor
  · -- Show 40 is in the set
    have h3 : ∃ c ∈ Ioo (0 : ℝ) (Real.pi / 2), c * sin c = 4 / 5 := by
      have h4 : (0 : ℝ) < Real.pi / 2 := by
        linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h5 : sin (0 : ℝ) = 0 := by
        simp
      have h6 : sin (Real.pi / 2) = 1 := by
        norm_num
      have h7 : ∃ c ∈ Icc (0 : ℝ) (Real.pi / 2), c * sin c = 4 / 5 := by
        have h8 : ContinuousOn (fun x : ℝ => x * sin x) (Icc 0 (Real.pi / 2)) := by
          apply Continuous.continuousOn
          continuity
        have h9 : (0 : ℝ) * sin (0 : ℝ) ≤ (4 / 5 : ℝ) := by
          rw [h5]
          norm_num
        have h10 : ((Real.pi / 2) : ℝ) * sin (Real.pi / 2) ≥ (4 / 5 : ℝ) := by
          rw [h6]
          nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
        have h11 : 4 / 5 ∈ Icc ((0 : ℝ) * sin (0 : ℝ)) ((Real.pi / 2) * sin (Real.pi / 2)) := by
          rw [h5] at *
          rw [h6] at *
          constructor
          · norm_num
          · -- Show that 4/5 ≤ π/2
            nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
        apply intermediate_value_Icc (by linarith [h4]) h8 h11
      rcases h7 with ⟨c, hc, hc1⟩
      rcases hc with ⟨hc3, hc4⟩
      have hc5 : c > 0 := by
        by_contra h
        push_neg at h
        have hc6 : c = 0 := by
          linarith
        rw [hc6] at hc1
        norm_num at hc1
      have hc6 : c < Real.pi / 2 := by
        by_contra h
        push_neg at h
        have hc7 : c = Real.pi / 2 := by
          linarith
        rw [hc7] at hc1
        have hc7' : sin (Real.pi / 2) = 1 := by
          norm_num
        rw [hc7'] at hc1
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      exact ⟨c, ⟨hc5, hc6⟩, hc1⟩
    rcases h3 with ⟨c, hc2, hc3⟩
    use c
    constructor 
    · -- Show c ∈ (0, Real.pi) 
      cases hc2 with 
      | intro h1 h2 => 
        constructor 
        · linarith 
        · -- Show c < Real.pi 
          nlinarith [Real.pi_gt_31415, Real.pi_lt_31416] 
    · -- Show that the expression is equal to 40 
      have hc4 : c * sin c = 4 / 5 := hc3
      have hc5 : 0 < c := by 
        linarith [hc2.1] 
      have hc6 : sin c > 0 := by 
        apply sin_pos_of_pos_of_lt_pi 
        all_goals 
          linarith [hc2.2, Real.pi_gt_31415, Real.pi_lt_31416] 
      have h7 : (25 * c ^ 2 * (sin c) ^ 2 + 16) / (c * sin c) = 40 := by
        have hc6' : c * sin c > 0 := by 
          nlinarith [hc6, hc5] 
        have hc7 : (25 * c ^ 2 * (sin c) ^ 2 + 16) ≥ 0 := by 
          nlinarith [sq_nonneg (c * sin c), sq_nonneg (c), sq_nonneg (sin c)]
        field_simp [show c * sin c ≠ 0 by nlinarith, show c ≠ 0 by linarith, show sin c ≠ 0 by linarith]
        <;> nlinarith [sq_nonneg (c * sin c - 4 / 5), sq_nonneg (5 * (c * sin c) - 4), sq_nonneg ((c * sin c) ^ 2 - (16 / 25)), sq_nonneg ((5 * c * sin c) ^ 2 - 16), Real.pi_gt_31415, Real.pi_lt_31416]
      linarith [h7]
  · -- Show that 40 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx, hy⟩
    rcases hx with ⟨hx1, hx2⟩
    have h3 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    have h4 : x * sin x > 0 := by
      nlinarith [h3, show x > 0 by linarith]
    have h5 : (25 * x ^ 2 * (sin x) ^ 2 + 16) / (x * sin x) ≥ 40 := by
      have h6 : (25 * x ^ 2 * (sin x) ^ 2 + 16) ≥ 40 * (x * sin x) := by
        nlinarith [sq_nonneg (5 * x * sin x - 4), sq_nonneg (x * sin x - 4 / 5), sq_nonneg ((x * sin x) * 5 - 4), sq_nonneg (x * sin x - 4 / 5), sq_nonneg (x - (4 / (5 * sin x))), sq_pos_of_pos h3, sq_pos_of_pos (show x > 0 by linarith), mul_pos (show x > 0 by linarith) h3]
      have h7 : x * sin x > 0 := by
        nlinarith [h3, show x > 0 by linarith]
      have h8 : (25 * x ^ 2 * (sin x) ^ 2 + 16) / (x * sin x) ≥ 40 := by
        apply (le_div_iff₀ h7).mpr
        linarith [h6]
      linarith [h8]
    linarith [h5, hy]