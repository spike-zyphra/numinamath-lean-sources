import Mathlib

open Real Set
open scoped Real

theorem algebra_150543 (φ : ℝ) (hφ : φ ∈ Ioo 0 (π/2)) :
    sin (cos φ) < cos φ ∧ cos φ < cos (sin φ) := by
  rcases hφ with ⟨h1, h2⟩
  have h3 : 0 < sin φ := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  
  have h4 : sin φ < 1 := by
    have h5 : sin φ < sin (π / 2) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos]
    have h6 : sin (π / 2) = 1 := sin_pi_div_two
    linarith [h5, h6]

  have h7 : 0 < cos φ := by
    apply cos_pos_of_mem_Ioo
    constructor
    all_goals linarith [Real.pi_pos]

  have h8 : cos φ < 1 := by
    have h9 : cos φ < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos]
    have h10 : cos (0 : ℝ) = 1 := by
      rw [cos_zero]
    linarith [h9, h10]

  -- Prove the first part: sin (cos φ) < cos φ
  have h16 : sin (cos φ) < cos φ := by
    have h17 : cos φ > 0 := h7
    have h18 : cos φ < Real.pi / 2 := by
      linarith [show Real.pi / 2 > (1 : ℝ) by linarith [Real.pi_gt_31415], h8]

    -- For y in (0, π/2), sin(y) < y.
    -- We know for y in (0, π/2), sin(y) < y.
    have h21 : cos φ > 0 := h7
    have h22 : cos φ < Real.pi := by linarith [Real.pi_gt_31415, h8]

    have h5 : sin (cos φ) < cos φ := by
      -- We know that for x in (0, π), sin(x) < x.
      -- Here, cos φ is in (0, 1) subset of (0, π).
      apply sin_lt
      all_goals linarith [Real.pi_gt_31415]

    linarith

  -- Prove the second part: cos φ < cos (sin φ)
  have h23 : sin φ < φ := by 
    -- We know that sin(x) < x for x > 0
    have h24 : sin φ < φ := by 
      have h25 : 0 < φ := h1
      -- We know for x in (0, π), sin x < x.
      have h60 : 0 < φ := h1
      have h61 : φ < Real.pi := by linarith [Real.pi_gt_31415, h2]
      -- Use sin x < x for x in (0, pi)
      have h62 : sin φ < φ := by
        have h7 : sin φ < φ := by 
          apply sin_lt
          all_goals linarith [Real.pi_gt_31415]
        linarith
      linarith
    linarith
  
  -- Use `sin φ < φ` and that `cos` is strictly decreasing on `(0, π)` to prove `cos φ < cos (sin φ)`
  have h24 : cos φ < cos (sin φ) := by 
    -- Since `cos` is strictly decreasing on `[0, π]`, and both `sin φ` and `φ` are in `[0, π]`
    have h28 : sin φ < φ := h23
    -- We need sin φ ≥ 0 and φ ≤ π
    have h29 : sin φ ≥ 0 := by linarith [show sin φ > 0 by apply sin_pos_of_pos_of_lt_pi; linarith; linarith]

    have h30 : φ ≤ Real.pi := by linarith [Real.pi_gt_31415, h2]

    -- Apply the fact about decreasing function
    have hcos : cos φ < cos (sin φ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals 
        nlinarith [h3, Real.pi_gt_31415, h4, h28]

    linarith

  -- Now, combine both parts.
  constructor
  · -- Show that sin (cos φ) < cos φ
    linarith [h16]
  · -- Show that cos φ < cos (sin φ)
    linarith [h24]