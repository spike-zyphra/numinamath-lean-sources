import Mathlib

/- (Five points) Determine whether the function $f(x) = x + \sin x$ where $x \in \mathbb{R}$ is an even function and a decreasing function, an even function and an increasing function, an odd function and a decreasing function, or an odd function and an increasing function.-/
theorem algebra_9117 {f : ℝ → ℝ} (hf : f = λ x => x + Real.sin x) :
    (∀ x, f (-x) = -f x) ∧ Monotone f := by
  constructor
  -- Verify that $f(x)$ is odd function.
  . intro x
    simp [hf]
    ring
  -- Prove that $f(x)$ is monotone by calculating its deriv.
  apply monotone_of_deriv_nonneg
  -- Show that $f(x)$ is differentiable.
  . rw [hf]
    intro x
    apply DifferentiableAt.add
    . exact differentiableAt_id'
    . exact Real.differentiableAt_sin
  -- Show that $f(x)\geq 0$ for all real numbers.
  intro x
  rw [hf, deriv_add, deriv_id'', Real.deriv_sin]
  have := Real.cos_mem_Icc x
  simp at this
  simpa using by linarith
  . exact differentiableAt_id'
  . exact Real.differentiableAt_sin
