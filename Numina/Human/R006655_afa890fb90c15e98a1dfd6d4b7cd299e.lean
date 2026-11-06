import Mathlib

open Real
/-
The price of a product was reduced by $1\%$ each year for $10000$ consecutive years. Let $X$ be the equivalent single percentage reduction that would achieve the same final price. This means that $(1 - 1/100)^{10000} = (1 - X/100)$. Show that $X = 100 \times (1 - (99/100)^{10000})$.
-/

theorem algebra_639715 (X:ℝ) (h: (1-1/100)^10000 = 1 - X / 100):
X = 100 * (1-(99/100)^10000) := by

  have eq1: (1:ℝ) - 1/100 = 99/100 := by norm_num
  rw [eq1] at h
  have eq2: X / 100 = 1 - (99/100)^10000 := by linarith
  have eq3: X = 100 * (1 - (99/100)^10000) := by linarith
  exact eq3
  