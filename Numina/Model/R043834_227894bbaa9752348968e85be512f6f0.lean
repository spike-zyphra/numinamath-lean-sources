import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21583 {g : ℝ → ℝ} (hg : g = λ x => -6 * sin (x * π / 6)) :
    g (g (-1)) = -6 := by
  have h1 : g (-1) = 3 := by
    rw [hg]
    have h2 : sin ((-1 : ℝ) * π / 6) = -1 / 2 := by
      have h3 : (-1 : ℝ) * π / 6 = -(π / 6) := by
        ring
      rw [h3]
      have h4 : sin (-(π / 6 : ℝ)) = -sin (π / 6 : ℝ) := by
        rw [sin_neg]
      rw [h4]
      rw [sin_pi_div_six]
      all_goals norm_num
    simp_all [h2]
    all_goals linarith
  have h5 : g 3 = -6 := by
    rw [hg]
    have h6 : sin ((3 : ℝ) * π / 6) = 1 := by
      have h7 : (3 : ℝ) * π / 6 = π / 2 := by
        linarith [Real.pi_pos]
      rw [h7]
      exact sin_pi_div_two
    simp_all [h6]
    all_goals linarith
  rw [h1]
  exact h5