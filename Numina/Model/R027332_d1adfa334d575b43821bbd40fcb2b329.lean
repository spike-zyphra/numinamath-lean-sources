import Mathlib

open Real Set
open scoped Real

theorem algebra_126092 (α : ℝ) (hα : α ∈ Ioo 0 (π/2)) :
    {x : ℝ | sin α ^ x + cos α ^ x = 1}.encard = 1 := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h2 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith
  have h3 : sin α < 1 := by
    have h4 : sin α < sin (π / 2) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [Real.pi_pos, hα1, hα2]
    have h5 : sin (π / 2) = 1 := by
      exact sin_pi_div_two
    linarith [h5, h4]
  have h4 : cos α < 1 := by
    have h5 : cos α < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals
        linarith [Real.pi_pos, hα1, hα2]
    have h6 : cos (0 : ℝ) = 1 := by
      exact cos_zero
    linarith [h6, h5]
  have h5 : sin α ^ (2 : ℝ) + cos α ^ (2 : ℝ) = 1 := by
    have h6 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have h7 : sin α ^ (2 : ℝ) + cos α ^ (2 : ℝ) = sin α ^ 2 + cos α ^ 2 := by
      simp
    rw [h7]
    linarith
  have h6 : ∀ x : ℝ, sin α ^ x + cos α ^ x = 1 ↔ x = 2 := by
    intro x 
    constructor 
    · -- First implication: If sin α ^ x + cos α ^ x = 1 then x = 2 
      intro h_eq
      by_cases h7 : x > (2 : ℝ)
      · -- Assume x > 2 
        have h8 : sin α ^ x < sin α ^ (2 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals
            linarith [h1, h3]
        have h9 : cos α ^ x < cos α ^ (2 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals
            linarith [h2, h4]
        have h10 : sin α ^ x + cos α ^ x < 1 := by
          have h11 : sin α ^ x + cos α ^ x < sin α ^ (2 : ℝ) + cos α ^ (2 : ℝ) := by
            linarith [h8, h9]
          nlinarith [h5, show sin α ^ (2 : ℝ) > 0 by nlinarith, show cos α ^ (2 : ℝ) > 0 by nlinarith]
        linarith [h10, h_eq]
      · -- Case $\neg(x > 2)$, so $x \leq 2$ 
        by_cases h7 : x < (2 : ℝ)
        · -- Assume x < 2 
          have h8 : sin α ^ x > sin α ^ (2 : ℝ) := by
            have h11 : sin α ^ (2 : ℝ) < sin α ^ x := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals
                linarith [h1, h3]
            linarith
          have h9 : cos α ^ x > cos α ^ (2 : ℝ) := by
            have h11 : cos α ^ (2 : ℝ) < cos α ^ x := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals
                linarith [h2, h4]
            linarith
          have h10 : sin α ^ x + cos α ^ x > 1 := by
            have h11 : sin α ^ x + cos α ^ x > sin α ^ (2 : ℝ) + cos α ^ (2 : ℝ) := by
              linarith [h8, h9]
            nlinarith [h5, show sin α ^ (2 : ℝ) > 0 by nlinarith, show cos α ^ (2 : ℝ) > 0 by nlinarith]
          linarith [h10, h_eq]
        · -- Case $\neg(x < 2)$, so $x \geq 2$ and $\neg(x > 2)$, hence $x = 2$ 
          have h10 : x = (2 : ℝ) := by
            linarith
          linarith
    · -- Second implication: x = 2 implies the equation 
      intro h_eq
      rw [h_eq]
      linarith [h5]
  have h7 : {x : ℝ | sin α ^ x + cos α ^ x = 1} = {2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    specialize h6 x
    tauto
  rw [h7]
  simp [Set.encard_singleton]