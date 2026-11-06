import Mathlib
open Real Set

theorem algebra_1099 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) (hcos : cos α + 2 * sin α = 2) :
    tan α = 3 / 4 := by
  rcases hα with ⟨h1, h2⟩
  have h3 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith [Real.pi_pos]

  have h4 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith [Real.pi_pos]

  have h5 : cos α = 2 - 2 * sin α := by linarith
  have h6 : cos α ^ 2 + sin α ^ 2 = 1 := by exact Real.cos_sq_add_sin_sq α
  rw [h5] at h6
  have h7 : 5 * sin α ^ 2 - 8 * sin α + 3 = 0 := by
    nlinarith

  have h8 : (5 * sin α - 3) * (sin α - 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.1 h8) with h9 h10
  · -- Case where $5 \sin \alpha - 3 = 0$, hence $\sin \alpha = 3/5$
    have hsin : sin α = 3 / 5 := by linarith
    have hcos : cos α = 4 / 5 := by
      nlinarith
    have htan : tan α = sin α / cos α := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan]
    rw [hsin, hcos]
    all_goals norm_num

  · -- Case where $\sin \alpha - 1 = 0$, i.e., $\sin \alpha = 1$
    have hsin1 : sin α = 1 := by linarith
    have h8 : sin α < 1 := by
      have h9 : sin (π / 2) = 1 := Real.sin_pi_div_two
      have h10 : sin α < sin (π / 2) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      linarith [h9, h10]
    linarith [hsin1, h8]