import Mathlib

/- Given the function $f(x)=x^{3}$, find the derivative of $f(-2)$, denoted as $[f(-2)]'$.-/
theorem algebra_9354 {f : ℝ → ℝ} (_ : f = fun x => x^3) (x : ℝ) :
    deriv (fun (x : ℝ) => f (-2)) x = 0 := by
  -- It's clear that deriv of constant function is 0.
  simp
