import Mathlib

/- The decreasing interval for the function $f(x)=x^{3}-3x^{2}+4$ is __________.-/
theorem algebra_9207 (f : ℝ → ℝ) (hf : f = fun x => x^3 - 3 * x^2 + 4) :
    StrictAntiOn f (Set.Ioo 0 2) := by
  -- We prove that $f(x)$ is strictly antimonotone on $(0, 2)$ by calculating its deriv.
  apply strictAntiOn_of_deriv_neg
  -- $(0,2)$ is convex.
  . exact convex_Ioo 0 2
  -- $f(x)$ is continuous on $(0,2)$.
  . rw [hf]
    apply ContinuousOn.add
    . apply ContinuousOn.sub
      . exact continuousOn_pow 3
      apply ContinuousOn.mul
      . exact continuousOn_const
      exact continuousOn_pow 2
    exact continuousOn_const
  -- Deriv of $f(x)$ is negtive on $(0,2)$.
  intro x hx
  simp [hf]
  rw [deriv_sub]
  simp at hx ⊢
  nlinarith
  . exact differentiableAt_pow 3
  . apply DifferentiableAt.mul
    . exact differentiableAt_const 3
    . exact differentiableAt_pow 2
