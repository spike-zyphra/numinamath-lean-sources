import Mathlib

/- Real numbers $a, b, c$ are not equal $0$ and are solution of the system:
$\begin{cases} a^2 + a =  b^2 \\ b^2 + b = c^2 \\ c^2  +c = a^2 \end{cases}$
Prove that $(a - b)(b - c)(c - a) = 1$. -/
theorem algebra_77260 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 + a = b^2) (h2 : b^2 + b = c^2) (h3 : c^2 + c = a^2) :
    (a - b) * (b - c) * (c - a) = 1 := by
  -- Using differences and equations
  apply mul_left_cancel₀ (sub_ne_zero.2 ha)
  -- Equivalent transformation to Nelling's given without using ring
  nlinarith [h1, h2, h3, sq (a - b), sq (b - c), sq (c - a)]