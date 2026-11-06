import Mathlib

open Finset

/- 9. The real numbers $x_{1}, x_{2}, x_{3}, \ldots, x_{30}$ satisfy the following conditions:


$$

\left\{\begin{array}{l}
20^{3} x_{1}+21^{3} x_{2}+22^{3} x_{3}+\cdots+49^{3} x_{30}=13 \\
21^{3} x_{1}+22^{3} x_{2}+23^{3} x_{3}+\cdots+50^{3} x_{30}=1 \\
22^{3} x_{1}+23^{3} x_{2}+24^{3} x_{3}+\cdots+51^{3} x_{30}=19
\end{array}\right.

$$


What is the value of $21 x_{1}+22 x_{2}+23 x_{3}+\cdots+50 x_{30}$?
(A) There are multiple acceptable values
(B) The system has no solution
(C) 1065
(D) 7
(E) 5 -/
theorem algebra_137332 (x : ℕ → ℝ)
    (h₁ : ∑ i ∈ range 30, (i + 20)^3 * x i = 13)
    (h₂ : ∑ i ∈ range 30, (i + 21)^3 * x i = 1)
    (h₃ : ∑ i ∈ range 30, (i + 22)^3 * x i = 19) :
    ∑ i ∈ range 30, (i + 21) * x i = 5 := calc
  -- Show that ∑ i ∈ [0, 30), (i + 21) x(i) = (∑ i ∈ [0, 30), ((i + 20)^3 - 2 * (i + 21)^3 + (i + 22)^3) * x(i)) / 6.
  _ = (∑ i ∈ range 30, ((i + 20)^3 - 2 * (i + 21)^3 + (i + 22)^3) * x i) / 6 := by
      field_simp
      rw [sum_mul]
      apply sum_congr rfl
      intro _ _
      -- It is enough to show that 6 * (i + 21) = (i + 20)^3 - 2 * (i + 21)^3 + (i + 22)^3.
      ring
  -- ∑ i ∈ [0, 30), ((i + 20)^3 - 2 * (i + 21)^3 + (i + 22)^3) * x(i)
  --    = ∑ i ∈ [0, 30), (i + 20)^3 * x(i) - 2 * ∑ i ∈ [0, 30), (i + 21)^3 * x(i) + ∑ i ∈ [0, 30), (i + 22)^3 * x(i)
  --    = 13 - 2 * 1 + 19.
  _ = (13 - 2 + 19) / 6 := by
      simp_rw [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, h₁, h₃]
      simp_rw [mul_assoc, ← mul_sum, h₂]
      norm_num
  -- (13 - 2 + 19) / 6 = 5.
  _ = 5 := by norm_num