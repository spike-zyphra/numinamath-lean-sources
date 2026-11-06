import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_323178 {f : ℝ → ℝ} (hf : f = λ x => exp x + 2 * x - 3) :
    f (1 / 2) * f 1 < 0 := by
  have h1 : f (1 / 2) = exp (1 / 2 : ℝ) + 2 * (1 / 2 : ℝ) - 3 := by
    rw [hf]
  have h2 : f 1 = exp (1 : ℝ) + 2 * (1 : ℝ) - 3 := by
    rw [hf]
  rw [h1, h2]
  have h3 : exp (1 / 2 : ℝ) < (2 : ℝ) := by
    have h4 : exp (1 / 2 : ℝ) < exp (Real.log 2) := by
      apply Real.exp_strictMono
      have h5 : Real.log 2 > (1 / 2 : ℝ) := by
        have h7 : Real.log 2 > (1 / 2 : ℝ) := by
          linarith [Real.log_two_lt_d9, Real.log_two_gt_d9]
        linarith
      linarith
    have h6 : exp (Real.log 2) = (2 : ℝ) := by
      rw [Real.exp_log]
      all_goals linarith
    linarith
  have h4 : exp (1 : ℝ) > (1 : ℝ) := by
    have h5 : exp (1 : ℝ) > exp (0 : ℝ) := by
      apply Real.exp_strictMono
      linarith
    have h6 : exp (0 : ℝ) = (1 : ℝ) := by
      simp
    linarith [h6]
  have h6 : exp (1 / 2 : ℝ) - (2 : ℝ) < (0 : ℝ) := by
    linarith [h3]
  have h7 : exp (1 : ℝ) - (1 : ℝ) > (0 : ℝ) := by
    linarith [h4]
  have h8 : (exp (1 / 2 : ℝ) + (2 * (1 / 2 : ℝ)) - 3) * (exp (1 : ℝ) + (2 * (1 : ℝ)) - 3) < (0 : ℝ) := by
    have h9 : exp (1 / 2 : ℝ) + (2 * (1 / 2 : ℝ)) - 3 = exp (1 / 2 : ℝ) - 2 := by
      ring_nf
    have h10 : exp (1 : ℝ) + (2 * (1 : ℝ)) - 3 = exp (1 : ℝ) - 1 := by
      ring_nf
    rw [h9, h10]
    have h11 : exp (1 / 2 : ℝ) - (2 : ℝ) < (0 : ℝ) := by
      linarith [h3]
    have h12 : exp (1 : ℝ) - (1 : ℝ) > (0 : ℝ) := by
      linarith [h4]
    nlinarith
  linarith [h8]