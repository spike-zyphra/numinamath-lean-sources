import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_325573 {α : ℝ} (hα : α ∈ Ioo 0 (π/2)) :
    {x : ℝ | sin α ^ x + cos α ^ x = 1}.encard = 1 := by
  rcases hα with ⟨hα1, hα2⟩
  have hsin1 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]

  have hsin2 : sin α < 1 := by
    have h1 : sin α < sin (π / 2 : ℝ) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [hα1, hα2, Real.pi_pos]
    have h2 : sin (π / 2 : ℝ) = 1 := by
      rw [sin_pi_div_two]
    linarith [h1, h2]
    
  have hcos1 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]

  have hcos2 : cos α < 1 := by
    have h1 : cos α < cos (0 : ℝ) := by
      apply cos_lt_cos_of_nonneg_of_le_pi
      all_goals
        linarith [hα1, hα2, Real.pi_pos]
    have h2 : cos (0 : ℝ) = 1 := by
      simp
    linarith [h1, h2]

  have h1 : {x : ℝ | sin α ^ x + cos α ^ x = 1} = {2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume $\sin^\x \alpha + \cos^\x \alpha = 1$, prove $x = 2$.
      intro h_eq
      by_cases h : x < 2
      · -- Assume x < 2, show that sin ^x α + cos ^x α > 1
        have h6 : sin α ^ x + cos α ^ x > 1 := by
          have h4 : sin α ^ (2 : ℝ) + cos α ^ (2 : ℝ) = 1 := by
            have hsin : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
            have h7 : sin α ^ (2 : ℝ) = (sin α) ^ 2 := by
              norm_cast
            have h8 : cos α ^ (2 : ℝ) = (cos α) ^ 2 := by
              norm_cast
            rw [h7, h8] at *
            all_goals
              linarith
          have h5 : (sin α: ℝ) ^ x + (cos α: ℝ) ^ x > (sin α: ℝ) ^ (2 : ℝ) + (cos α: ℝ) ^ (2 : ℝ) := by
            have h5s : sin α ^ x > (sin α) ^ (2 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals
                try linarith
                try positivity
            have h5c : (cos α) ^ x > (cos α: ℝ) ^ (2 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals
                try linarith
                try positivity
            linarith
          linarith [h4]
        linarith [h_eq, h6]
      by_cases h' : x > 2
      · -- Assume x > 2, show that sin ^x α + cos ^x α < 1
        have h10 : sin α ^ x + cos α ^ x < 1 := by
          have h4 : sin α ^ (2 : ℝ) + cos α ^ (2 : ℝ) = 1 := by
            have h6 : sin α ^ (2 : ℝ) = (sin α) ^ 2 := by
              norm_cast
            have h7 : cos α ^ (2 : ℝ) = (cos α) ^ 2 := by
              norm_cast
            rw [h6, h7]
            exact Real.sin_sq_add_cos_sq α
          have h5 : (sin α: ℝ) ^ x + (cos α: ℝ) ^ x < (sin α: ℝ) ^ (2 : ℝ) + (cos α: ℝ) ^ (2 : ℝ) := by
            have h5s : sin α ^ x < sin α ^ (2 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals
                try linarith
                try positivity
            have h5c : cos α ^ x < cos α ^ (2 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals
                try linarith
                try positivity
            linarith
          linarith [h4]
        linarith [h_eq, h10]
      have h_eq2 : x = (2 : ℝ) := by linarith
      assumption
    · -- Assume x = 2, show that sin ^x α + cos ^x α = 1.
      intro h_eq
      rw [h_eq]
      have h4 : sin α ^ (2 : ℝ) + cos α ^ (2 : ℝ) = 1 := by
        have h6 : sin α ^ (2 : ℝ) = (sin α) ^ 2 := by
          norm_cast
        have h7 : cos α ^ (2 : ℝ) = (cos α) ^ 2 := by
          norm_cast
        rw [h6, h7]
        exact Real.sin_sq_add_cos_sq α
      simpa using h4
  rw [h1]
  simp [Set.encard_singleton]