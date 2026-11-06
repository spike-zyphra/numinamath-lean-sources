import Mathlib

/- Let $n$ be a positive integer and let $a, b, c, d$ be integers such that $n \mid a+b+c+d$ and $n \mid a^{2}+b^{2}+c^{2}+d^{2}$. Show that

$$
n \mid a^{4}+b^{4}+c^{4}+d^{4}+4 a b c d .
$$ -/
theorem number_theory_605820 (n : ℤ) (hn : n > 0) (a b c d : ℤ)
    (h1 : n ∣ a + b + c + d) (h2 : n ∣ a^2 + b^2 + c^2 + d^2) :
    n ∣ a^4 + b^4 + c^4 + d^4 + 4 * a * b * c * d := by
  -- Let p(x) := (x - a)(x - b)(x - c)(x - d) = x^4 + A * x^3 + B * x^2 + C * x + D
  -- We have that A = -(a + b + c + d), B = a * b + a * c + a * d + b * c + b * d + c * d, C = -(a * b * c + a * b * d + a * c * d + b * c * d), D = a * b * c * d
  let A := -(a + b + c + d)
  let B := a * b + a * c + a * d + b * c + b * d + c * d
  let C := -(a * b * c + a * b * d + a * c * d + b * c * d)
  -- By calculating p(a) + p(b) + p(c) + p(d) we get that
  -- a^4 + b^4 + c^4 + d^4 + A * (a^3 + b^3 + c^3 + d^3) + B * (a^2 + b^2 + c^2 + d^2) + C * (a + b + c + d) + 4 * D = 0
  -- So a^4 + b^4 + c^4 + d^4 + 4 * a * b * c * d = -A * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - B * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) - C * (a + b + c + d)
  have H : a^4 + b^4 + c^4 + d^4 + 4 * a * b * c * d = -A * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - B * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) - C * (a + b + c + d) := by ring
  -- So a^4 + b^4 + c^4 + d^4 + 4 * a * b * c * d is a linear combination of a + b + c + d, a^2 + b^2 + c^2 + d^2, and we are done
  rw [H]
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨l, hl⟩
  use (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) * k - B * l - C * k
  linear_combination
    (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 - C) * hk - B * hl
