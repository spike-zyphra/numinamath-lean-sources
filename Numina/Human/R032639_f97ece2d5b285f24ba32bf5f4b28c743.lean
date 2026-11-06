import Mathlib

/-
Problem

Given that $f(x)$ is an even function and is decreasing on $(0, +\infty)$, determine the monotonicity of $f(x)$ on $(-\infty, 0)$ and prove it.
-/

/-
Solution

The function $f(x)$ is increasing on $(-\infty, 0)$. Let $x_1 < x_2 < 0$, since $f(x)$ is an even function, we have $f(-x_1) = f(x_1)$ and $f(-x_2) = f(x_2)$. Given the assumption, we know $-x_1 > -x_2 > 0$. Since it is known that $f(x)$ is decreasing on $(0, +\infty)$, we have $f(-x_1) < f(-x_2)$, which implies $f(x_1) < f(x_2)$. Therefore, it can be concluded that the function $f(x)$ is increasing on $(-\infty, 0)$. Thus, the final answer is $\boxed{\text{increasing}}$.
-/


theorem algebra_9293 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
 (hfd : ∀ x y, (x > 0) ∧ (y > 0) ∧ (x > y) → f x < f y) :
    ∀ x y, (x < 0) ∧ (y < 0) ∧ (x > y) → f x > f y := by
      intro x y ⟨xle0, yle0, xgey⟩
      rw [← hf x, ← hf y]
      -- since $x < 0$
      have nx : -x > 0  := by aesop
      -- and since $y < 0$
      have ny : -y > 0  := by aesop
      have xy : -y > -x := by aesop
      -- by assumption $f$ is decreasing in $(0, \infinity)$ and $-y > -x$, so we have the following result
      obtain foo := hfd (-y) (-x) ⟨ny, nx, xy⟩
      exact foo