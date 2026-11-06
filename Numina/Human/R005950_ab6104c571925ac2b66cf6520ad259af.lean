import Mathlib

/- Find $x$ if $x^{x^{x^{*}}}=2$. -/
theorem algebra_610874 :
  let f (x' x : ℝ) := x' ^ x
  ∃ (x : ℝ), Function.IsFixedPt (f x) 2 :=
by
  -- The question is simply saying, there exists a value $x$ such that $2$ is the fixed point of the function $x ^ -$.
  use Real.sqrt 2
  simp [Function.IsFixedPt]
