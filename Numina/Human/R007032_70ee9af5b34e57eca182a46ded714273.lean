import Mathlib

/--
Mary is about to pay for five items at the grocery store.  The prices of the items are $7.99$, $4.99$, $2.99$, $1.99$, and $0.99$.  Mary will pay with a twenty-dollar bill.  Which of the following is closest to the percentage of the $20.00$ that she will receive in change?
$\text {(A) } 5 \qquad \text {(B) } 10 \qquad \text {(C) } 15 \qquad \text {(D) } 20 \qquad \text {(E) } 25$
-/
theorem algebra_1174 : ((20 : ℚ) - 7.99 - 4.99 - 2.99 - 1.99 - 0.99) / 20.00 * 100.00 = 5.25 := by
  -- The total price of the items is $(8-.01)+(5-.01)+(3-.01)+(2-.01)+(1-.01)=19-.05=18.95$
  rw [(by norm_num : (20 : ℚ) - 7.99 - 4.99 - 2.99 - 1.99 - 0.99 = (20 : ℚ) - 18.95)]
  -- $20-18.95=1.05$
  rw [(by norm_num : (20 : ℚ) - 18.95 = 1.05)]
  -- $\frac{1.05}{20}=.0525 \Rightarrow \text{(A)}$
  norm_num