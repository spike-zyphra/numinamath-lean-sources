import Mathlib

/- Let the line $p$ be the perpendicular bisector of $A = (24, 7)$ and $B = (3, 4).$ Given that $AB$ meets $p$ at $C = (x, y),$ what is $2x - 4y$? -/
theorem algebra_15613 {A B C : ℝ × ℝ}
    (hA : A = (24, 7)) (hB : B = (3, 4))
    (hC : C = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) :
    2 * C.1 - 4 * C.2 = 5 := by
  subst_vars
  norm_num