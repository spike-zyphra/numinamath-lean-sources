import Mathlib

open Real Set
open scoped Real

theorem inequalities_291182 (x : ℝ) (hx : 0 < x ∧ x < π / 2) :
    sin (cos x) < cos (sin x) := by
  rcases hx with ⟨hx1, hx2⟩
  have h3 : 0 < cos x := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, hx1, hx2]
    · linarith [Real.pi_pos, hx1, hx2]
  have h4 : 0 < sin x := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      linarith [Real.pi_pos, hx1, hx2]
  have h5 : cos x < 1 := by
    have h6 : cos x < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals
        linarith [Real.pi_pos, hx1, hx2]
    have h7 : cos (0 : ℝ) = 1 := by
      exact Real.cos_zero
    nlinarith

  have h6 : sin x < 1 := by
    have h7 : sin x < sin (π / 2 : ℝ) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [Real.pi_pos, hx1, hx2]
    have h8 : sin (π / 2 : ℝ) = 1 := Real.sin_pi_div_two
    linarith

  have h8 : sin (cos x) < cos (sin x) := by
    have h9 : cos (sin x) = sin (Real.pi / 2 - sin x) := by
      rw [show cos (sin x) = sin (Real.pi / 2 - sin x) by 
        rw [← sin_pi_div_two_sub]
        <;> ring_nf <;> norm_num
      ]
    rw [h9] at *
    have h11 : cos x > 0 := by linarith [h3]
    have h13 : sin x > 0 := by linarith [h4]

    have h12 : cos x < Real.pi / 2 - sin x := by
      have h14 : sin x > 0 := by linarith [h4]
      have h15 : cos x > 0 := by linarith [h3]
      have h16 : sin x + cos x < Real.pi / 2 := by
        have h17 : sin x + cos x < Real.pi / 2 := by
          have h18 : sin x > 0 := by linarith [show sin x > 0 by apply sin_pos_of_pos_of_lt_pi; all_goals linarith [Real.pi_pos, hx1, hx2]]
          have h19 : cos x > 0 := by linarith [show cos x > 0 by apply cos_pos_of_mem_Ioo; all_goals constructor <;> linarith [Real.pi_pos, hx1, hx2]]
          nlinarith [Real.sin_sq_add_cos_sq x, Real.pi_gt_three, Real.pi_pos, 
            hx1, hx2, 
            show sin x > 0 by apply sin_pos_of_pos_of_lt_pi; all_goals linarith [Real.pi_pos, hx1, hx2], 
            show cos x > 0 by apply cos_pos_of_mem_Ioo; all_goals constructor <;> linarith [Real.pi_pos, hx1, hx2]
          ]
        linarith
      linarith
    have h14 : sin (cos x) < sin (Real.pi / 2 - sin x) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        nlinarith [Real.pi_pos, Real.sin_sq_add_cos_sq x, h3, h4, h5, h6, 
          Real.sin_le_one (Real.pi / 2 - sin x), Real.sin_le_one (cos x), Real.cos_le_one (x)
        ]
    linarith [h14]
  linarith [h8]