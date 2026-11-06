import Mathlib
/-Suppose $f (x ) = x^2 + 12$. If $m > 0$ and $f (3m) = 3(f (m))$, what is the value of $m$?-/
theorem algebra_21116 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 + 12) (m : ℝ) (hm : m > 0)
    (h : f (3 * m) = 3 * f m) : m = 2 := by
    --We have $f(3m) = (3m)^2 + 12 = 9m^2 + 12$, so $f(3m) = 3f(m)$ gives us $9m^2 + 12 = 3(m^2 + 12)$.  Expanding the right side gives $9m^2 +12 = 3m^2 + 36$.
    simp only [hf] at h; ring_nf at h
    --Simplifying gives $6m^2 = 24$, so $m^2 = 4$.
    have e := congrArg ( fun (n) => ((n) -12 - m ^ 2 * 3) / 6 ) h; beta_reduce at e; ring_nf at e; rw [show (4 : ℝ) = 2 ^ 2 by ring_nf] at e
    --Since we are given that $m>0$, we have $m = \boxed{2}$.
    rw [sq_eq_sq₀] at e ;exact e
    --Combining the condition m>0
    linarith
    linarith
