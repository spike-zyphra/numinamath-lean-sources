import Mathlib

theorem algebra_219212 {f : ℝ → ℝ} (h1 : ∀ x, f (2 + x) = f (2 - x)) (h2 : ∀ x, f (5 + x) = f (5 - x)) :
    ∀ x, f (x + 6) = f x := by
  -- From $h1$: $∀ x, f (2 + x) = f (2 - x)$, we derive $f(t) = f(4 - t)$ for all $t$
  have h3 : ∀ t, f t = f (4 - t) := by
    intro t
    have h1' := h1 (t - 2)
    rw [show (2 + (t - 2 : ℝ)) = t by ring, show (2 - (t - 2 : ℝ)) = (4 - t) by ring] at h1'
    linarith [h1']
  -- From $h2$: $∀ x, f (5 + x) = f (5 - x)$, we derive $f(t) = f(10 - t)$ for all $t$
  have h4 : ∀ t, f t = f (10 - t) := by
    intro t
    have h2' := h2 (t - 5)
    rw [show (5 + (t - 5 : ℝ)) = t by ring, show (5 - (t - 5 : ℝ)) = (10 - t) by ring] at h2'
    linarith [h2']
  -- Show that $f(x + 6) = f(x)$ using the derived properties
  intro x
  have eq1 : f (x + 6) = f (4 - x) := by
    have eq2 := h4 (x + 6)
    rw [show 10 - (x + 6 : ℝ) = (4 - x) by ring] at eq2
    linarith
  have eq2 : f x = f (4 - x) := by
    specialize h3 x
    linarith
  linarith [eq1, eq2]