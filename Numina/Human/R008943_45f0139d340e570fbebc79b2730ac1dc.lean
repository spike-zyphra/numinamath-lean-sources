import Mathlib

/-
  Given that $f(x)$ is an odd function, and
  $g(x) = f(x) + 9$, if $g(-2) = 3$, then $f(2) = \boxed{6}$.
-/
theorem algebra_9400 {f g : ℝ → ℝ} (hodd : ∀ x, f (-x) = - f x) (hg : g = fun x => f x + 9) (hg2 : g (-2) = 3) :
    f 2 = 6 := by
  -- apply the definition of g
  have h1 : g (-2) = f (- 2) + 9 := by simp [hg]
  -- apply the definition of odd
  have h2 : f (-2) = - f 2 := by exact hodd 2
  rw [h2, hg2] at h1
  -- solve
  linear_combination h1
