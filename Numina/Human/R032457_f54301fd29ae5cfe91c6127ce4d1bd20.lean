import Mathlib

/- Given the function $f(x) = \dfrac{\sqrt{4-x^2}}{|x+3|-3}$, if $f(a) = -4$, then the value of $f(-a)$ is _______. -/
theorem algebra_9035 {f : ℝ → ℝ} (hf : f = fun x => √(4 - x ^ 2) / (|x + 3| - 3)) (a : ℝ) (dom_a : 4 - a ^ 2 ≥ 0 ∧ |a + 3| - 3 ≠ 0)
    (ha : f a = -4) : f (-a) = 4 := by
  -- The domain of f is -2 ≤ a ≤ 2 and a ≠ 0
  replace dom_a : -2 ≤ a ∧ a ≤ 2 ∧ a ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩
    . nlinarith
    . nlinarith
    . -- If a = 0, then abs (a + 3) - 3 = 0
      intro h
      subst a
      simp at dom_a
  -- Expand the definition of f
  rw [congrFun hf] at ha ⊢
  -- a + 3 and -a + 3 are both positive, so we can simplify the absolute values
  rw [abs_of_pos (by linarith)] at ha ⊢
  -- Simplify the expression
  simp at ha ⊢
  rw [div_neg]
  linarith
