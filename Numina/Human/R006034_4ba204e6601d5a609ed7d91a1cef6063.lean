import Mathlib

/- Suppose $f$ is a function that assigns to each real number $x$ a value $f(x)$, and suppose the equation

$$
f\left(x_{1}+x_{2}+x_{3}+x_{4}+x_{5}\right)=f\left(x_{1}\right)+f\left(x_{2}\right)+f\left(x_{3}\right)+f\left(x_{4}\right)+f\left(x_{5}\right)-8
$$

holds for all real numbers $x_{1}, x_{2}, x_{3}, x_{4}, x_{5}$. What is $f(0)$ ?-/
theorem algebra_611218 (f : ℝ → ℝ) (h : ∀ x : Fin 5 → ℝ, f (x 0 + x 1 + x 2 + x 3 + x 4) = f (x 0) + f (x 1) + f (x 2) + f (x 3) + f (x 4) - 8) : f 0 = 2 := by
  -- Plug in x 0 = x 1 = x 2 = x 3 = x 4 = 0.
  let s : Fin 5 → ℝ := fun i => 0
  specialize h s
  simp [s] at h
  -- Direct simplification from f 0 = 5 f 0 - 8.
  linarith
  