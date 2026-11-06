import Mathlib
open Real
/- The check for a luncheon of 3 sandwiches, 7 cups of coffee and one piece of pie came to 3.15\$.The check for a luncheon consisting of 4 sandwiches,10 cups of coffee and one piece of pie cameto
4.20 \$ at the same place. The cost of a luncheon consisting of one sandwich, one cup of coffee, and one piece of pie at the same place will come to
$\textbf{(A)}\ 1.70 \qquad \textbf{(B)}\ 1.65 \qquad \textbf{(C)}\ 1.20 \qquad \textbf{(D)}\ 1.05 \qquad \textbf{(E)}\ 0.95$-/
theorem algebra_97260 (s c p : ℝ) (h1 : 3*s+7*c+p=3.15) (h2 : 4*s+10*c+p=4.20) : s+c+p=1.05 := by
--Let $s$ be the cost of one sandwich,c be the cost of one cup of coffee, and p be the price of one piece of pie.  With the information.
--Substracting the first equation from the second equation gives $s+3c=1.05$.
  have h3:s+3*c=1.05:=by
    linear_combination h2-h1
--This is equivalent to $s=1.05-3c$.
  replace h3:s=1.05-3*c:=by rw[←h3];ring
--Substitute this into the first equation to get $p=2c$.
  rw[h3] at h2
  ring_nf at h2
  rw[←sub_eq_zero] at h2
  ring_nf at h2
  rw[add_comm,←sub_eq_add_neg,sub_eq_zero] at h2
--Substitute the relations of $s,p$ to $c$ into the desired equation gives the final answer.
  rw[h2,h3]
  ring