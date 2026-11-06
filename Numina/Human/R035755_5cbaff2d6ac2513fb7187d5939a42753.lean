import Mathlib

/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f\left(x^{2} y\right)=f(x y)+y f(f(x)+y)
$$

for all real numbers $x$ and $y$. -/
theorem algebra_606142 : {f : ℝ → ℝ | ∀ x y, f (x ^ 2 * y) = f (x * y) + y * f (f x + y)} =
    {fun _ => 0} := by
  ext f
  simp
  constructor
  . intro hf
    -- set $x = 0$ in `hf`, we get $yf(f(0)+y)=0$
    specialize hf 0
    simp at hf
    -- set $x = 0 \and y=-f(0) $ in `hf`, we get $f(0)=0$
    have f_0_eq_0 : f 0 = 0 := by
      have h := hf (- f 0)
      simp at h
      exact h
    -- so we get $\forall y \ne 0, f(y)=0$
    rw [f_0_eq_0] at hf
    simp at hf
    ext x
    -- consider $x = 0$ and $x \ne 0$ separately.
    by_cases hx : x = 0
    -- When $x = 0$, we have $f(0)=0$
    . rw [hx]
      exact f_0_eq_0
    -- When $x \ne 0$, we have $\forall y \ne 0, f(y)=0$ from above
    . specialize hf x
      simp [hx] at hf
      exact hf
  -- check $f(x) = 0$ is a solution
  . intro hf
    rw [hf]
    simp
