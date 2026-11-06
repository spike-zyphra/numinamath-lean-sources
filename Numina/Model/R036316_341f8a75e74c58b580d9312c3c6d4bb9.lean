import Mathlib
open Polynomial
theorem algebra_21707 {r s t : ℝ} (h :∀ p : Polynomial ℝ, p.natDegree = 2 → ∀ n : ℤ, Polynomial.eval (↑n : ℝ) p= r * Polynomial.eval ↑(n - 1) p + s * Polynomial.eval ↑(n - 2) p + t * Polynomial.eval ↑(n - 3) p) : (r, s, t) = (3, -3, 1):= by
  have eq1 := h (X^2) (by
      compute_degree!
    ) 0
  simp [Polynomial.eval_X] at eq1
  have eq2 := h (X^2) (by
      compute_degree!
    ) 1
  simp [Polynomial.eval_X] at eq2
  have eq3 := h (X^2) (by
      compute_degree!
    ) 2
  simp [Polynomial.eval_X] at eq3
  have eq4 := h (X^2) (by
      compute_degree!
    ) 3
  simp [Polynomial.eval_X] at eq4
  have ht : t = 1 := by
    nlinarith
  have hs : s = -3 := by
    nlinarith [ht]
  have hr : r = 3 := by
    nlinarith [ht, hs]
  simp [Prod.ext_iff, ht, hs, hr]
  <;> tauto