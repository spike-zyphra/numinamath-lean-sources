import Mathlib

open Real Set
open scoped Real

theorem calculus_15614 :
  {x : ℝ | x ∈ Icc (-1) 1 ∧ arccos x > arcsin x} = Ico (-1) (1 / √ 2) := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ico]
  constructor
  · -- Assume x ∈ {x : ℝ | x ∈ Icc (-1) 1 ∧ arccos x > arcsin x}
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : -1 ≤ x := h1.1
    have h4 : x ≤ 1 := h1.2
    have h5 : arccos x + arcsin x = Real.pi / 2 := by 
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      all_goals linarith
    have h6 : arcsin x < Real.pi / 4 := by
      nlinarith [h2, h5]
    have h7 : x < (1 : ℝ) / Real.sqrt 2 := by
      have h8 : arcsin x < Real.pi / 4 := h6
      have h9 : Real.sin (arcsin x) < Real.sin (Real.pi / 4) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          nlinarith [Real.pi_gt_three, Real.pi_pos, arcsin_le_pi_div_two x, neg_pi_div_two_le_arcsin x]
      have h10 : Real.sin (arcsin x) = x := by 
        rw [Real.sin_arcsin]
        all_goals 
          nlinarith [h1.1, h1.2]
      have h11 : Real.sin (Real.pi / 4) = (1 : ℝ) / Real.sqrt 2 := by 
        field_simp [Real.sin_pi_div_four]
      nlinarith [h11, h10, h9, Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)]
    constructor
    · linarith
    · -- Show that x < 1/√2
      linarith
  · -- Assume x ∈ Ico (-1) (1 / √ 2)
    rintro ⟨h1, h2⟩
    constructor
    · -- Show x ∈ Icc (-1) 1
      constructor
      · -- Show -1 ≤ x
        linarith
      · -- Show x ≤ 1
        have h3 : x < (1 : ℝ) / Real.sqrt 2 := h2
        have h4 : (1 : ℝ) / Real.sqrt 2 < (1 : ℝ) := by 
          have h5 : Real.sqrt 2 > 1 := by 
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          apply (div_lt_iff₀ (by positivity)).mpr
          nlinarith [h5]
        linarith [h3, h4]
    · -- Show arccos x > arcsin x
      have h3 : -1 ≤ x := h1
      have h4 : x ≤ (1 : ℝ) := by
        have h5 : x < (1 : ℝ) / Real.sqrt 2 := h2
        have h6 : (1 : ℝ) / Real.sqrt 2 < (1 : ℝ) := by 
          have h5 : Real.sqrt 2 > 1 := by 
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          apply (div_lt_iff₀ (by positivity)).mpr
          nlinarith [h5]
        linarith [h5, h6]
      have h7 : arcsin x < Real.pi / 4 := by
        have h8 : x < (1 : ℝ) / Real.sqrt 2 := h2
        have h9 : Real.sin (Real.pi / 4) = (1 : ℝ) / Real.sqrt 2 := by 
          field_simp [Real.sin_pi_div_four]
        have h10 : Real.sin (arcsin x) = x := by 
          rw [Real.sin_arcsin]
          all_goals 
            nlinarith [h3, show x ≤ 1 by linarith [h4]]
        by_contra h
        push_neg at h
        have h12 : Real.sin (arcsin x) ≥ Real.sin (Real.pi / 4) := by
          apply Real.sin_le_sin_of_le_of_le_pi_div_two
          all_goals
            nlinarith [Real.pi_gt_three, Real.pi_pos, arcsin_le_pi_div_two x, neg_pi_div_two_le_arcsin x, h]
        nlinarith [h10, h9, h12, Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)]
      have h8 : arccos x + arcsin x = Real.pi / 2 := by 
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]
        all_goals 
          linarith
      nlinarith [h8, h7]