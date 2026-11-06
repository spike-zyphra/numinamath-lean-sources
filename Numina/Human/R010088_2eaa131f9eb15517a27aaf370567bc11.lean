import Mathlib

/- A cubic polynomial $p(x)$ satisfies
\[p(n) = \frac{1}{n^2}\]for $n = 1, 2, 3,$ and $4.$  Find $p(5).$ -/
theorem algebra_15182 {p : ℝ → ℝ} (hp : ∃ a b c d, p = fun x => a*x^3 + b*x^2 + c*x + d)
    (h1 : p 1 = 1 / 1 ^ 2) (h2 : p 2 = 1 / 2 ^ 2) (h3 : p 3 = 1 / 3 ^ 2)
    (h4 : p 4 = 1 / 4 ^ 2) : p 5 = -5 / 12 := by
  obtain ⟨a, b, c, d, rfl⟩ := hp
  norm_num at h1 h2 h3 h4
  linarith