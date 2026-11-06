import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_308979 : IsLeast {x | ∃ t : ℝ, x = abs (cos t) + abs (cos (2 * t))} (sqrt 2 / 2) := by
  constructor
  · -- Show that sqrt 2 / 2 is in the set
    use Real.pi / 4
    have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h2 : cos (2 * (Real.pi / 4)) = 0 := by
      have h1' : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
      rw [h1']
      exact cos_pi_div_two
    rw [h1, h2]
    have h3 : 0 ≤ Real.sqrt 2 / 2 := by
      have h4 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith [show Real.sqrt 2 ≥ 0 by positivity]
    have h4 : abs (Real.sqrt 2 / 2) = Real.sqrt 2 / 2 := by
      apply abs_of_nonneg
      linarith [h3]
    have h5 : abs (0 : ℝ) = 0 := by
      simp
    rw [h4, h5]
    all_goals linarith
  · -- Show that sqrt 2 / 2 is a lower bound
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : cos (2 * t) = 2 * cos t ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h1] at ht
    by_cases h4 : cos t ≥ 0
    · -- We need $|\cos t| \geq 0$ and $|\cos 2t| \geq 0$
      have h5 : abs (cos t) = cos t := by
        rw [abs_of_nonneg h4]
      by_cases h6 : 2 * cos t ^ 2 - 1 ≥ 0
      · -- When $2 * \cos t ^ 2 - 1 \geq 0$, we have $|2 * \cos t ^ 2 - 1| = 2 * \cos t ^ 2 - 1$
        have h7 : abs (2 * cos t ^ 2 - 1) = 2 * cos t ^ 2 - 1 := by
          rw [abs_of_nonneg h6]
        rw [h5, h7] at ht
        nlinarith [sq_nonneg (cos t - Real.sqrt 2 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg (cos t + Real.sqrt 2 / 2)]
      · -- When $2 * \cos t ^ 2 - 1 < 0$, we have $|2 * \cos t ^ 2 - 1| = 1 - 2 * \cos t ^ 2$
        have h7 : abs (2 * cos t ^ 2 - 1) = 1 - 2 * cos t ^ 2 := by
          rw [abs_of_neg (by linarith)]
          all_goals linarith
        rw [h5, h7] at ht
        nlinarith [sq_nonneg (cos t - Real.sqrt 2 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg (cos t + Real.sqrt 2 / 2)]
    · -- cos t < 0
      have h5 : abs (cos t) = - cos t := by
        rw [abs_of_neg (by linarith)]
      by_cases h6 : 2 * cos t ^ 2 - 1 ≥ 0
      · -- When $2 * \cos t ^ 2 - 1 \geq 0$, we have $|2 * \cos t ^ 2 - 1| = 2 * \cos t ^ 2 - 1$
        have h7 : abs (2 * cos t ^ 2 - 1) = 2 * cos t ^ 2 - 1 := by
          rw [abs_of_nonneg h6]
        rw [h5, h7] at ht
        nlinarith [sq_nonneg (cos t + Real.sqrt 2 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg (cos t - Real.sqrt 2 / 2)]
      · -- When $2 * \cos t ^ 2 - 1 < 0$, we have $|2 * \cos t ^ 2 - 1| = 1 - 2 * \cos t ^ 2$
        have h7 : abs (2 * cos t ^ 2 - 1) = 1 - 2 * cos t ^ 2 := by
          rw [abs_of_neg (by linarith)]
          all_goals linarith
        rw [h5, h7] at ht
        nlinarith [sq_nonneg (cos t + Real.sqrt 2 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg (cos t - Real.sqrt 2 / 2)]