import Mathlib

/- A merchant bought some goods at a discount of $20\%$ of the list price. He wants to mark them at such a price that he can give a discount of $20\%$ of the marked price and still make a profit of $20\%$ of the selling price. The per cent of the list price at which he should mark them is:
$(A)  20(B)  100(C)  125(D)  80(E)  120$ -/
theorem algebra_94203 {c l s m : ℝ} (lpos:0<l) (h1:c=0.8*l) (h2:s=c+0.2*s) (h3:s=0.8*m) : m/l=1.25 := by
--Let $C$ represent the cost of the goods, and let $L$, $S$, and $M$ represent the list, selling, and marked prices of the goods, respectively. Hence, we have three equations, which we need to manipulate in order to relate $M$ and $L$
  rw[h1,h3,←sub_eq_iff_eq_add] at h2
--Substitute $C=0.8L$ and $S=0.8M$ into the equation $S=C+0.2S$
  ring_nf at h2
  norm_num
  field_simp at h2 ⊢
  linarith
--Simplify the equation we get the desired result.
--We find that $L=1.25C$, so the answer is $\boxed{\textbf{(C) } 125}$.