import Mathlib

theorem algebra_139315 (f : ℝ → ℝ) (h : ∀ x, f (x ^ 2 + 4 * x) = abs (x + 2)) :
    ∀ x, x ∈ Set.Ici (-4) → f x = Real.sqrt (x + 4) := by
  intro x hx
  have h1 : -4 ≤ x := by
    simpa using hx
  have h2 : ∀ t : ℝ, f (t ^ 2 + 4 * t) = abs (t + 2) := by
    intro t
    have ht := h t
    simpa using ht
  -- We need to find some real number $t$ such that $t^2 + 4t = x$ and then apply the functional equation to find $f(x)$.

  -- From solving the quadratic equation $t^2 + 4t - x = 0$, we get two possible solutions: $t = -2 \pm \sqrt(x + 4)$.

  -- Let's verify with $t = -2 + \sqrt(x + 4)$.

  -- Compute $t + 2$: $-2 + \sqrt(x + 4) + 2 = \sqrt(x + 4)$

  -- Then $|t + 2| = |\sqrt(x + 4)| = \sqrt(x + 4)$. This is exactly what we want to prove.

  -- To apply the functional equation, we need that $t^2 + 4 t = x$, which we just verified. So $f(x) = |t + 2| = \sqrt(x + 4)$. Let's complete the formal proof:
  have h3 : f x = Real.sqrt (x + 4) := by
    have h4 : f ((-2 + Real.sqrt (x + 4)) ^ 2 + 4 * (-2 + Real.sqrt (x + 4))) = abs ((-2 + Real.sqrt (x + 4)) + 2) := by
      apply h2
    have h5 : (-2 + Real.sqrt (x + 4)) ^ 2 + 4 * (-2 + Real.sqrt (x + 4)) = x := by
      nlinarith [Real.sqrt_nonneg (x + 4), Real.sq_sqrt (show (0 : ℝ) ≤ x + 4 by linarith)]
    have h7 : abs ((-2 + Real.sqrt (x + 4)) + 2) = Real.sqrt (x + 4) := by
      have h8 : (-2 + Real.sqrt (x + 4)) + 2 = Real.sqrt (x + 4) := by
        ring
      rw [h8]
      all_goals simp
    have h8 : f ((-2 + Real.sqrt (x + 4)) ^ 2 + 4 * (-2 + Real.sqrt (x + 4)) ) = Real.sqrt (x + 4) := by
      rw [h4, h7]
    -- Since $((-2 + Real.sqrt (x + 4)) ^ 2 + 4 * (-2 + Real.sqrt (x + 4))) = x$ from h5, it follows that $f(x) = Real.sqrt(x + 4)$:
    have h9 : f x = Real.sqrt (x + 4) := by
      have eq2 : ((-2 + Real.sqrt (x + 4)) ^ 2 + 4 * (-2 + Real.sqrt (x + 4)) ) = x := h5
      rw [show ((-2 + Real.sqrt (x + 4)) ^ 2 + 4 * (-2 + Real.sqrt (x + 4)) ) = x by linarith [eq2] ] at h8
      linarith
    linarith
  exact h3