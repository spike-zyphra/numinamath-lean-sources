import Mathlib

open Real Set
open scoped Real

theorem inequalities_29260 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    sin (cos α) < cos (sin α) := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : sin (cos α) < cos (sin α) := by
    have h2 : cos (sin α) = sin (Real.pi / 2 - sin α) := by
      rw [← sin_pi_div_two_sub]
    rw [h2]
    have h3 : 0 < cos α := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [hα1, hα2, Real.pi_pos]
      · linarith [hα1, hα2, Real.pi_pos]
    have h4 : cos α < 1 := by
      have h5 : cos α < cos (0 : ℝ) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals
          linarith [hα1, hα2, Real.pi_pos]
      have h6 : cos (0 : ℝ) = 1 := by
        simp [cos_zero]
      linarith [h5, h6]
    have h8 : sin α > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith [hα1, Real.pi_pos]
      · linarith [hα1, hα2, Real.pi_pos]
    have h9 : sin α < 1 := by
      have h10 : sin α < sin (Real.pi / 2) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [hα1, hα2, Real.pi_pos]
      have h11 : sin (Real.pi / 2) = 1 := by
        rw [sin_pi_div_two]
      linarith [h10, h11]
    have h10 : cos α + sin α < Real.pi / 2 := by
      have h11 : cos α ^ 2 + sin α ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq α
      have h12 : (cos α + sin α) ^ 2 ≤ 2 := by
        nlinarith [h11, sq_nonneg (cos α - sin α)]
      have h13 : cos α + sin α ≤ Real.sqrt 2 := by
        have h14 : Real.sqrt 2 ^ 2 = 2 := by
          rw [Real.sq_sqrt]
          linarith
        have h15 : (cos α + sin α) ^ 2 ≤ Real.sqrt 2 ^ 2 := by
          linarith [h12, h14]
        have h16 : 0 ≤ Real.sqrt 2 := by
          positivity
        have h17 : cos α + sin α ≥ 0 := by
          nlinarith [h3, h8]
        nlinarith [sq_nonneg (cos α + sin α - Real.sqrt 2), Real.sqrt_nonneg 2]
      have h14 : Real.sqrt 2 < Real.pi / 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.pi_gt_31415, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.pi_pos]
      nlinarith [h13, h14, h12, Real.sqrt_nonneg 2]
    have h3 : cos α < Real.pi / 2 - sin α := by
      nlinarith [h10]
    have h4 : cos α ∈ Icc (0 : ℝ) (Real.pi / 2) := by
      constructor
      · -- 0 ≤ cos α
        nlinarith [h3, Real.pi_pos]
      · -- cos α ≤ π/2
        nlinarith [h3, Real.pi_pos]
    have h5 : Real.pi / 2 - sin α ∈ Icc (0 : ℝ) (Real.pi / 2) := by
      constructor
      · -- 0 ≤ π/2 - sin α
        nlinarith [h8, Real.pi_pos]
      · -- π/2 - sin α ≤ π/2
        nlinarith [h8, Real.pi_pos]
    have h6 : sin (cos α) < sin (Real.pi / 2 - sin α) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      · -- Show 0 ≤ cos α ≤ π/2
        cases h4 with
        | intro h4l h4r =>
          all_goals linarith
      · -- Show 0 ≤ π/2 - sin α ≤ π/2
        cases h5 with
        | intro h5l h5r =>
          all_goals linarith
      · -- Show cos α < π/2 - sin α
        linarith [h3]
    exact h6
  exact h1