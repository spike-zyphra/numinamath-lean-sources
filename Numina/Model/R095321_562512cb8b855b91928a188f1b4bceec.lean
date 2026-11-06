import Mathlib

open Real Set
open scoped Real

theorem algebra_100145 (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    arcsin x < arccos x ↔ x ∈ Ico (-1) (Real.sqrt 2 / 2) := by
  constructor
  · -- Assume arcsin x < arccos x, prove x ∈ Ico (-1) (Real.sqrt 2 / 2)
    intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : arcsin x < arccos x := h
    have h2 : arcsin x < Real.pi / 4 := by
      have h3 : arccos x = Real.pi / 2 - arcsin x := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      rw [h3] at h1
      linarith [Real.pi_pos]
    have h4 : x < Real.sqrt 2 / 2 := by
      have h5 : x = Real.sin (arcsin x) := by
        rw [Real.sin_arcsin]
        all_goals linarith [hx1, hx2]
      have h6 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact Real.sin_pi_div_four
      have h7 : arcsin x < Real.pi / 4 := h2
      have h8 : x < Real.sin (Real.pi / 4) := by
        rw [h5]
        have h9 : Real.sin (arcsin x) < Real.sin (Real.pi / 4) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            linarith [Real.pi_pos, Real.pi_gt_three, Real.arcsin_le_pi_div_two x, Real.neg_pi_div_two_le_arcsin x]
        linarith [h9]
      linarith [h6, h8]
    constructor
    · linarith
    · linarith [h4]
  · -- Assume x ∈ Ico (-1) (Real.sqrt 2 / 2), prove arcsin x < arccos x
    rintro ⟨hx1, hx2⟩
    have h3 : x < Real.sqrt 2 / 2 := hx2
    rcases hx with ⟨hx1', hx2'⟩
    have h4 : arcsin x < Real.pi / 4 := by
      have h5 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact Real.sin_pi_div_four
      have h6 : Real.sin (arcsin x) = x := by
        rw [Real.sin_arcsin]
        all_goals linarith [hx1', hx2']
      have h7 : Real.sin (arcsin x) < Real.sin (Real.pi / 4) := by
        nlinarith [h5, h6, h3, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.pi_pos, Real.pi_gt_three]
      have h8 : arcsin x < Real.pi / 4 := by
        by_contra h
        push_neg at h
        have h9 : Real.sin (arcsin x) ≥ Real.sin (Real.pi / 4) := by
          apply Real.sin_le_sin_of_le_of_le_pi_div_two
          all_goals
            nlinarith [Real.pi_pos, Real.pi_gt_three, Real.arcsin_le_pi_div_two x, Real.neg_pi_div_two_le_arcsin x, h]
        nlinarith [h5, h6, h9]
      linarith [h8]
    have h9 : arccos x = Real.pi / 2 - arcsin x := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    linarith [h9, h4]