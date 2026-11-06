import Mathlib

/- Let $e(x)$ be an even function, and let $o(x)$ be an odd function, such that
\[e(x) + o(x) = \frac{6}{x + 2} + x^2 + 2^x\]for all real numbers $x \neq -2.$  Find $o(1).$ -/
theorem algebra_18793 {e o : ℝ → ℝ} (he : ∀ x, e (-x) = e x)
    (ho : ∀ x, o (-x) = -o x) (h : ∀ x ≠ -2, e x + o x = 6 / (x + 2) + x ^ 2 + 2 ^ x) :
    o 1 = -5 / 4 := by
  have he' := h (-1)
  have ho' := h 1
  simp [he, ho] at he' ho'
  norm_num at he' ho'
  linarith