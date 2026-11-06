import Mathlib

/- Simplify $\frac{3a^2b}{5ac}\times\frac{10c}{6ab}$, given that $a,b,c\neq0.$ -/
theorem algebra_20682 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (3 * a ^ 2 * b / (5 * a * c)) * (10 * c / (6 * a * b)) = 1 := by
  field_simp
  ring_nf
