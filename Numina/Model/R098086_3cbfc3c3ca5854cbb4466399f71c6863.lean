import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_256346 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (3 - 2*x - x^2)) :
    StrictAntiOn f {x | -3 < x ∧ x < -1} ∧ StrictMonoOn f {x | -1 < x ∧ x < 1} := by 
  constructor
  · -- Proof that f is strictly antimonotone (decreasing) on {x | -3 < x ∧ x < -1}
    intro x hx y hy hxy
    have hx1 : -3 < x := hx.1
    have hx2 : x < -1 := hx.2
    have hy1 : -3 < y := hy.1
    have hy2 : y < -1 := hy.2
    have h1 : x < y := hxy
    have h2 : 3 - 2 * x - x^2 > 0 := by
      nlinarith
    have h3 : 3 - 2 * y - y^2 > 0 := by
      nlinarith
    have h4 : 3 - 2 * x - x^2 < 3 - 2 * y - y^2 := by
      nlinarith
    rw [hf]
    simp at *
    have h5 : logb (1 / 2) (3 - 2 * x - x^2) > logb (1 / 2) (3 - 2 * y - y^2) := by
      apply logb_lt_logb_of_base_lt_one
      all_goals 
        nlinarith
    linarith
  · -- Proof that f is strictly monotone (increasing) on {x | -1 < x ∧ x < 1}
    intro x hx y hy hxy
    have hx1 : -1 < x := hx.1
    have hx2 : x < 1 := hx.2
    have hy1 : -1 < y := hy.1
    have hy2 : y < 1 := hy.2
    have h1 : x < y := hxy
    have h2 : 3 - 2 * x - x^2 > 0 := by
      nlinarith
    have h3 : 3 - 2 * y - y^2 > 0 := by
      nlinarith
    have h4 : 3 - 2 * x - x^2 > 3 - 2 * y - y^2 := by
      nlinarith
    rw [hf]
    simp at *
    have h5 : logb (1 / 2) (3 - 2 * x - x^2) < logb (1 / 2) (3 - 2 * y - y^2) := by
      apply logb_lt_logb_of_base_lt_one
      all_goals 
        nlinarith
    linarith