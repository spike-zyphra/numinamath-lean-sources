import Mathlib

/-Let $x,$ $y,$ and $z$ be nonzero complex numbers such that $x + y + z = 20$ and
\[(x - y)^2 + (x - z)^2 + (y - z)^2 = xyz.\]Find $\frac{x^3 + y^3 + z^3}{xyz}.$-/
theorem algebra_13554 {x y z : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
(h1 : x + y + z = 20) (h2 : (x - y)^2 + (x - z)^2 + (y - z)^2 = x * y * z) :
(x^3 + y^3 + z^3) / (x * y * z) = 13 := by
-- Rewrite the assumption h2
  ring_nf at h2
-- Prove the following auxillary lemma
  have : 2 * (x^3 + y^3 + z^3 - 3 * x * y * z) = (x + y + z) *
  (-(x * y * 2) - x * z * 2 + (x ^ 2 * 2 - y * z * 2) + y ^ 2 * 2 + z ^ 2 * 2) := by ring
-- Plug in h1, h2 to this and simplify
  rw [h1, h2] at this; apply_fun (fun x => x / 2) at this
  nth_rw 5 [mul_comm] at this; nth_rw 2 [mul_div_assoc] at this
  norm_num at this; apply_fun (fun t => t + 3 * x * y * z) at this
  ring_nf at this
-- Rewrite the final goal and prove it
  rw [div_eq_iff, mul_comm]; assumption
  repeat apply mul_ne_zero
  all_goals assumption