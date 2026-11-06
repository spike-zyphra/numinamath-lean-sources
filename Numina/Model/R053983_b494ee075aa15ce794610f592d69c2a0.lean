import Mathlib

open Real Set
open scoped Real

theorem algebra_260498 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (arcsin x)^2 - 2 * arcsin x - 2) :
  IsGreatest (range f) (Real.pi^2 / 4 + Real.pi - 2) := by

  constructor
  · -- Show that it is in the range
    use -1
    rw [h₀]
    have h1 : arcsin (-1 : ℝ) = -(Real.pi / 2) := by 
      rw [Real.arcsin_neg, Real.arcsin_one]
      all_goals linarith 
    rw [h1]
    all_goals nlinarith [Real.pi_pos, Real.pi_gt_three]
  · -- Show that it is the greatest
    intro y
    rintro ⟨x, hx⟩
    rw [h₀] at hx 
    have h2 : -(Real.pi / 2) ≤ arcsin x := by 
      apply Real.neg_pi_div_two_le_arcsin
    have h3 : arcsin x ≤ Real.pi / 2 := by 
      apply Real.arcsin_le_pi_div_two
    nlinarith [Real.pi_pos, Real.pi_gt_three, 
      sq_nonneg (arcsin x + Real.pi / 2), 
      sq_nonneg (arcsin x - Real.pi / 2)]