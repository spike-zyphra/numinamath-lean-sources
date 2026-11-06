import Mathlib

/- Calculate: $\left( \frac{1}{2}+\frac{1}{3}+\cdots +\frac{1}{1997} \right)\left( 1+\frac{1}{2}+\cdots +\frac{1}{1996} \right)$-\left( 1+\frac{1}{2}+\cdots +\frac{1}{1997} \right)\left( \frac{1}{2}+\frac{1}{3}+\cdots +\frac{1}{1996} \right)=$ ___          ___. -/
theorem algebra_1016 : (∑ i in Finset.range 1997, (1 / (i + 1))) * (∑ i in Finset.range 1996, (1 / (i + 1))) -
    (∑ i in Finset.range 1997, (1 / (i + 1))) * (∑ i in Finset.range 1996, (1 / (i + 1))) = 1 / 1997 := by
  native_decide