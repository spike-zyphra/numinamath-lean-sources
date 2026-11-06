import Mathlib
/-Compute $121_3+2122_3-1200_3-2111_3$. Express your answer in base 3.-/
theorem number_theory_22783 : (Nat.ofDigits 3 [1,2,1]) +  (Nat.ofDigits 3 [2,2,1,2]) -
    (Nat.ofDigits 3 [0,0,2,1]) - (Nat.ofDigits 3 [1,1,1,2]) = -Nat.ofDigits 3 [1,2,2] := by
    --It doesn't matter the order in which we add and subtract values, but we'll start with $2122_3-2111_3$ since the values are close. $$ \begin{array}{c@{}c@{\;}c@{}c@{}c@{}c} & & 2& 1 & 2 & 2_3\\ &- & 2 & 1 & 1 & 1_3\\ \cline{2-6} & & & & 1 & 1_3\\ \end{array} $$Now we're left with  $121_3-1200_3+11_3$. We add $121_3+11_3$. $$ \begin{array}{c@{}c@{\;}c@{}c@{}c@{}c} & & & 1 & 2 & 1_3\\ &+ & & & 1 & 1_3\\ \cline{2-6} & & & 2 & 0 & 2_3\\ \end{array} $$So we have $202_3-1200_3=-(1200_3-202_3)$. $$ \begin{array}{c@{}c@{\;}c@{}c@{}c@{}c} & & 1 & 2 & 0 & 0_3\\ &-& & 2 & 0 & 2_3\\ \cline{2-6} & & & 2 & 2 & 1_3\\ \end{array} $$Our answer is $\boxed{-221_3}$.
    --Convert ternary numbers to decimal numbers and validate them
    norm_num [Nat.ofDigits, List.foldr, List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
