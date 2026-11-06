import Mathlib

open Real

/- Let $x_1,x_2,x_3,x_4,x_5$ ve non-negative real numbers, so that
$x_1\le4$ and 
$x_1+x_2\le13$ and
$x_1+x_2+x_3\le29$ and
$x_1+x_2+x_3+x_4\le54$ and
$x_1+x_2+x_3+x_4+x_5\le90$.
Prove that $\sqrt{x_1}+\sqrt{x_2}+\sqrt{x_3}+\sqrt{x_4}+\sqrt{x_5}\le20$. -/
theorem inequalities_56778 (x : Fin 5 → ℝ)
    (h₀ : ∀ i, 0 ≤ x i)
    (h₁ : x 0 ≤ 4)
    (h₂ : x 0 + x 1 ≤ 13)
    (h₃ : x 0 + x 1 + x 2 ≤ 29)
    (h₄ : x 0 + x 1 + x 2 + x 3 ≤ 54)
    (h₅ : x 0 + x 1 + x 2 + x 3 + x 4 ≤ 90) :
    sqrt (x 0) + sqrt (x 1) + sqrt (x 2) + sqrt (x 3) + sqrt (x 4) ≤ 20 := by 
  -- For simplicity, we will relate term calculations on squares within each of these bounds.
  -- Because squares are turncated by non-linear correlations, evaluate the sum associatively quadractingants aligned.
  nlinarith [sq_sqrt (h₀ 0), sq_sqrt (h₀ 1), sq_sqrt (h₀ 2), sq_sqrt (h₀ 3), sq_sqrt (h₀ 4), 
             sq_nonneg (sqrt (x 0) - 2 * 1), sq_nonneg (sqrt (x 1) - 3 * 1), 
             sq_nonneg (sqrt (x 2) - 4 * 1), sq_nonneg (sqrt (x 3) - 5 * 1),
             sq_nonneg (sqrt (x 4) - 6 * 1)]