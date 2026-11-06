import Mathlib

/- \section*{Problem 4 - 071234}

Let $y=f(x)$ be a function defined for all real numbers $x$, which satisfies the following equation for all such $x$:


$$

f(x+1)=(x+1) \cdot f(x)

$$


Furthermore, let $y=g(x)$ be another function defined for all real $x$. For all $x$, $f(x)$ is not equal to 0.

Prove!

The function $\phi(x)=f(x) \cdot g(x)$ satisfies the equation


$$

\phi(x+1)=(x+1) \phi(x)

$$


for all real $x$ if and only if $g(x)$ is a periodic function with period 1. -/
theorem algebra_196435 {f g : ℝ → ℝ} (hf : ∀ x, f (x + 1) = (x + 1) * f x) (f_ne_zero : ∀ x, f x ≠ 0) :
    (∀ x, f (x + 1) * g (x + 1) = (x + 1) * f x * g x) ↔ Function.Periodic g 1 := by
  constructor
  -- assume the functional equation is satisfied
  · intro h x
    specialize h x
    -- rewrite the hypothesis using functional equation for f and divide by f (x + 1) since it is nonzero
    rw [←hf x] at h
    exact mul_left_cancel₀ (f_ne_zero (x + 1)) h
  -- conversely, we can conclude using the periodicity of g and the functional equation for f
  intro h x
  rw [h x, hf x]