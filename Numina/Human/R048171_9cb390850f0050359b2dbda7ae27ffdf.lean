import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-- Let $f_n (x) = \text{sin}^n x + \text{cos}^n x.$ -/
noncomputable def f (n : ℕ) (x : ℝ) := (sin x)^n + (cos x)^n

/-- Let $f_n (x) = \text{sin}^n x + \text{cos}^n x.$ For how many $x$ in $[0,\pi]$ is it true that
\[6f_{4}(x)-4f_{6}(x)=2f_{2}(x)?\]
$\text{(A) }2 \qquad \text{(B) }4  \qquad \text{(C) }6 \qquad \text{(D) }8 \qquad \text{(E) more
than }8$ -/
theorem algebra_1130 : ∀ x, 6 * (f 4 x) - 4 *(f 6 x) = 2 * (f 2 x) := by
  dsimp [f]
  intro x

  -- Write the even powers of $\text{cos} x$ in terms of $\text{cos}^2 x$.
  have : (cos x)^4 = ((cos x)^2) * ((cos x)^2) := by ring
  rw [this]

  have : (cos x)^6 = ((cos x)^2) * ((cos x)^2) * ((cos x)^2) := by ring
  rw [this]

  -- We will use the fundamental trigonometric identity $\sin^2{x} + \cos^2{x} = 1$
  -- to write everything in terms of $\text{sin} x$.
  have : (cos x)^2 = 1 - (sin x)^2 := by
    calc _ = (cos x)^2 + (sin x)^2 - (sin x)^2 := by ring
         _ = 1 - (sin x)^2 := by rw [cos_sq_add_sin_sq]
  rw [this]

  -- By simple algebra, we see that the equation holds for any $x$, so there are
  -- infinitely many solutions.
  ring