import Mathlib

/- Show that


$$

(x-a)^{2}(b-c)+(x-b)^{2}(c-a)+(x-c)^{2}(a-b)

$$


can be factored into a product of three linear factors independent of $x$. -/
theorem algebra_288581 {a b c : ℝ} :
    (x - a)^2 * (b - c) + (x - b)^2 * (c - a) + (x - c)^2 * (a - b) = -(a-b)*(b-c)*(c-a) := by
  -- we just calculate
  calc (x - a) ^ 2 * (b - c) + (x - b) ^ 2 * (c - a) + (x - c) ^ 2 * (a - b)
  _ = (x^2-2*a*x+a^2)*(b-c)+(x^2-2*b*x+b^2)*(c-a)+(x^2-2*c*x+c^2)*(a-b) := by ring
  _ = x^2*(b-c+c-a+a-b) -x*(2*a*b-2*a*c+2*b*c-2*a*b+2*a*c-2*b*c) + a^2*(b-c)+b^2*(c-a)+c^2*(a-b) := by ring_nf
  _ = a^2*(b-c)+b^2*(c-a)+c^2*(a-b) := by ring_nf
  _ = a^2*(b-c)+b^2*c-a*b^2+a*c^2-b*c^2 := by ring_nf
  _ = a^2*(b-c)+b*c*(b-c)-a*(b^2-c^2) := by ring_nf
  _ = (b-c)*(a^2+b*c-a*b-a*c) := by ring_nf
  _ = (b-c)*(a*(a-c)-b*(a-c)) := by ring_nf
  _ = (b-c)*(a-c)*(a-b) := by ring_nf
  _ = -(a-b)*(b-c)*(c-a) := by ring_nf