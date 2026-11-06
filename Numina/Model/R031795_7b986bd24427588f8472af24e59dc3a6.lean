import Mathlib

theorem algebra_9354 {f : ℝ → ℝ} (_ : f = fun x => x^3) (x : ℝ) :
    deriv (fun (x : ℝ) => f (-2)) x = 0 := by
  simp [deriv_const]