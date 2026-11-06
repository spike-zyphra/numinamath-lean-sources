import Mathlib

/-
Given that $f(x)$ is an even function and is decreasing on $(0, +\infty)$, determine the monotonicity of $f(x)$ on $(-\infty, 0)$ and prove it.
-/

theorem algebra_9293 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
 (hfd : ∀ x y, (x > 0) ∧ (y > 0) ∧ (x > y) → f x < f y) :
    ∀ x y, (x < 0) ∧ (y < 0) ∧ (x > y) → f x > f y := by
  intro x y ⟨xlt0, ylt0, xgey⟩
  have hx : f x = f (-x) := by
    specialize hf x
    linarith 
  have hy : f y = f (-y) := by
    specialize hf y 
    linarith
  have h1 : -x > 0 := by linarith 
  have h2 : -y > 0 := by linarith
  have h3 : -y > -x := by linarith
  have h4 : f (-y) < f (-x) := by
    have h6 : f (-y) < f (-x) := by
      apply hfd
      constructor
      · -- Show that $-y > 0$
        linarith 
      constructor
      · -- Show that $-x > 0$
        linarith 
      · -- Show that $-y > -x$
        linarith
    exact h6
  linarith [hx, hy, h4]