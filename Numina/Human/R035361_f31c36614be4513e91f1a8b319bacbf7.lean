import Mathlib

/-Evaluate $1234_5+2341_5$. Express your answer in base 5.-/
theorem number_theory_19553 (h: x1 = Nat.ofDigits 5 [4,3,2,1]) (h2: x2 =  Nat.ofDigits 5 [1,4,3,2]) : Nat.digits 5 (x1+x2) = [0,3,1,4]:= by
  --We have$\begin{array}{@{}c@{\;}c@{}c@{}c@{}c@{}c}& & 1 & 2 & 3 & 4_{5}\\ +& & 2& 3 & 4 & 1_{5}\\ \cline{1-6}&& 4 & 1 & 3 & 0 _{5}\\ \end{array}$
  --So, the final answer is $\boxed{4130_5}$.
    rw [Nat.ofDigits_eq_foldr] at h ;norm_num at h
    rw [Nat.ofDigits_eq_foldr] at h2 ;norm_num at h2
    rw [h];rw [h2]
    ring_nf
    native_decide
