import Mathlib

open Real Set
open scoped Real

theorem algebra_195415 :
  IsGreatest {x | ∃ θ : ℝ, x = (sin (3 * θ))^2 / 2 - (cos (2 * θ)) / 2} 1 := by
  constructor
  · -- Show that 1 belongs to the set
    use Real.pi / 2
    have h1 : sin (3 * (Real.pi / 2)) = -1 := by
      have h11 : 3 * (Real.pi / 2) = Real.pi + Real.pi / 2 := by ring
      rw [h11]
      have h12 : sin (Real.pi + Real.pi / 2) = -1 := by
        rw [sin_add]
        have hpi : sin Real.pi = 0 := by
          exact sin_pi
        have hpip2 : cos (Real.pi / 2) = 0 := by
          exact cos_pi_div_two
        have hpim : cos Real.pi = -1 := by
          exact cos_pi
        have hpis2 : sin (Real.pi / 2) = 1 := by
          exact sin_pi_div_two
        simp only [hpi, hpip2, hpim, hpis2] at *
        all_goals linarith
      exact h12
    have h2 : cos (2 * (Real.pi / 2)) = -1 := by
      have h21 : 2 * (Real.pi / 2) = Real.pi := by ring
      rw [h21]
      exact cos_pi
    rw [h1, h2]
    norm_num
  · -- Show that 1 is an upper bound
    intro x hx
    rcases hx with ⟨θ, h_eq⟩
    have h1 : (sin (3 * θ)) ^ 2 ≤ 1 := by
      apply sin_sq_le_one
    have h2 : cos (2 * θ) ≤ 1 := by
      apply cos_le_one
    have h3 : cos (2 * θ) ≥ -1 := by
      linarith [neg_one_le_cos (2 * θ), cos_le_one (2 * θ)]
    have h4 : (sin (3 * θ)) ^ 2 / 2 - (cos (2 * θ)) / 2 ≤ 1 := by
      nlinarith [sq_nonneg (sin (3 * θ) - 1), sq_nonneg (cos (2 * θ) + 1),
        h1, h2, h3, Real.sin_sq_add_cos_sq (3 * θ), Real.sin_sq_add_cos_sq (2 * θ),
        Real.sin_sq_add_cos_sq (θ), sq_nonneg (sin θ - 0), sq_nonneg (cos θ - 0)
      ]
    linarith [h_eq, h4]