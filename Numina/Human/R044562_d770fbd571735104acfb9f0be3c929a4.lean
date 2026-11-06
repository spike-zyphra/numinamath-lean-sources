import Mathlib
open Real
/- Given $x \in \mathbb{R}^+$, prove that $\sqrt{x} + \frac{6}{x-3} \ge 4$. Consider the case where $x = 1$ as a potential counterexample. Provide a detailed proof and identify any potential flaws in the following proof:

Let $t = \sqrt{x}$. Then, the inequality becomes:
\[ t + \frac{6}{t^2 - 3} \ge 4 \]
\[ t(t^2 - 3) + 6 \ge 4(t^2 - 3) \]
\[ t^3 - 4t^2 - 3t + 18 \ge 0 \]
\[ (t - 3)^2(t + 2) \ge 0 \]

Discuss the validity of this proof and determine the correct range of $x$ for which the inequality holds.-/


theorem inequalities_5173 (x : ℝ) (hx : x > 3) :
    sqrt x + 6 / (x - 3) ≥ 4 := by 
  have h1 : x - 3 > 0 := by linarith
  /-  Let $t = \sqrt{x}$. Since $x \in \mathbb{R}^+$, it follows that $t \geq 0$ and $t \neq \sqrt{3}$.-/
  have h2 : sqrt x > 0 := by
    apply sqrt_pos.2
    linarith
  have h3 : sqrt x ^ 2 = x := by
    exact sq_sqrt (by linarith)
  /- 1. The inequality $\\sqrt{x} + \\frac{6}{x-3} \\ge 4$ can be rewritten in terms of $t$ as: \[ t + \\frac{6}{t^2 - 3} \\ge 4 \]
2. Multiply both sides of the inequality by $t^2 - 3$ (noting that $t^2 - 3 \\neq 0$): \[ t(t^2 - 3) + 6 \\ge 4(t^2 - 3) \]-/
  have h4 : sqrt x + 6 / (x - 3) - 4 = (sqrt x - 3) ^ 2 * (sqrt x + 2) / (x - 3) := by 
    field_simp [h1, h2]
    nlinarith [h3, sq_nonneg (sqrt x), mul_self_nonneg (sqrt x - 3)]
  have h5 : (sqrt x - 3) ^ 2 * (sqrt x + 2) / (x - 3) ≥ 0 := by 
    apply div_nonneg
    apply mul_nonneg
    · nlinarith [sq_nonneg (sqrt x)]
    · nlinarith [h2]
    · nlinarith [h1]
  linarith [h4, h5]