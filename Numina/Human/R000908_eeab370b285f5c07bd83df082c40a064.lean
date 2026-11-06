import Mathlib

/- If the digits represented by $A$ and $B$ (which are not both $0$) satisfy the following addition problem $$ \begin{array}{c@{}c@{\;}c@{}c@{}c@{}c} & & & & A & B_7\\ &+ & & & B & A_7\\ \cline{2-6} & & & A & A & 0_7\\ \end{array} $$what is the product of the digits represented by $A$ and $B$? -/
theorem number_theory_19022 {A B : ℕ} (hA : A < 8) (hB : B < 8)
    (hAB : A ≠ 0 ∨ B ≠ 0) (h : A * 10 + B = B * 10 + A + 1) :
    A * B = 6 := by 
  omega