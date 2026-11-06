import Mathlib

open Real

theorem inequalities_599324 (θ : ℝ) (x y : ℝ) (hx : 0 < x) (hy : θ < y) :
    1 / (1 + x) ≥ 1 / (1 + y) - 1 / (1 + y) ^ 2 * (x - y) := by
  have h1 : 0 < 1 + x := by linarith

  by_cases h2 : 1 + y = 0
  · -- Case where 1 + y = 0, so y = -1
    have hy_eq : y = -1 := by linarith
    rw [hy_eq]
    simp
    all_goals linarith
  · -- Case where 1 + y ≠ 0, so we can manipulation fractions
    have h3 : 1 + y ≠ 0 := h2

    have h4 : 0 < (1 + y) ^ 2 := by
      apply pow_two_pos_of_ne_zero
      exact h3

    have h5 : 0 < (1 + x) * (1 + y) ^ 2 := by 
      positivity

    have h6 : 1 / (1 + x) - (1 / (1 + y) - 1 / (1 + y) ^ 2 * (x - y)) ≥ 0 := by
      have h7 : 1 / (1 + x) - (1 / (1 + y) - 1 / (1 + y) ^ 2 * (x - y)) =
          ( (x - y) ^ 2 ) / ( (1 + x) * (1 + y) ^ 2 ) := by 
        field_simp [(show 1 + x ≠ 0 by nlinarith), (show 1 + y ≠ 0 by 
          intro h
          apply h3
          linarith
        ), (show (1 + y) ≠ 0 by 
          intro h
          apply h3
          linarith
        )]
        <;> ring
      rw [h7]

      apply div_nonneg
      · -- Show that (x - y) ^ 2 ≥ 0
        apply pow_two_nonneg
      · -- Show that (1 + x) * (1 + y) ^ 2 > 0
        positivity

    linarith