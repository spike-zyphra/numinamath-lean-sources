import Mathlib

open Real Set
open scoped Real

theorem inequalities_103125 (φ : ℝ) (hφ : φ ∈ Ioo 0 (π/2)) :
    sin (cos φ) < cos φ ∧ cos φ < cos (sin φ) := by
  rcases hφ with ⟨h1, h2⟩
  have hcos1 : 0 < cos φ := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h1, Real.pi_pos]
    · linarith [h2, Real.pi_pos]

  have hcos2 : sin (cos φ) < cos φ := by
    have h4 : cos φ > 0 := hcos1
    have h5 : sin (cos φ) < cos φ := by
      have h7 : 0 < cos φ := h4
      have h8 : cos φ < Real.pi / 2 := by
        have h9 : cos φ < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h1, h2, Real.pi_pos]
        have h10 : cos (0 : ℝ) = 1 := by
          simp
        nlinarith [h9, h10, Real.pi_gt_three]
      apply sin_lt
      all_goals linarith
    linarith

  have h3 : sin φ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h1, h2, Real.pi_pos]

  have h5 : cos φ < cos (sin φ) := by
    have h4 : sin φ < φ := by
      apply sin_lt
      all_goals linarith
    have h6 : sin φ ≥ 0 := by
      linarith [h3]
    have h7 : sin φ ≤ Real.pi / 2 := by
      have h5a : sin φ < 1 := by
        have h11 : sin φ < sin (Real.pi / 2) := by
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [h1, h2, Real.pi_pos]
        have h12 : sin (Real.pi / 2) = 1 := by
          exact sin_pi_div_two
        nlinarith [h11, h12]
      have h8 : sin φ < (Real.pi / 2 : ℝ) := by
        nlinarith [h5a, Real.pi_pos]
      nlinarith
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    all_goals
      nlinarith [Real.pi_pos]

  constructor
  · -- Proof of first inequality `sin (cos φ) < cos φ`
    linarith [hcos2]
  · -- Proof of second inequality `cos φ < cos (sin φ)`
    linarith [h5]