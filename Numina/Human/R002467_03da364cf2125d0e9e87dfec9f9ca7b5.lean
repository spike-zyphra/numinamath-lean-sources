import Mathlib
/-- In a certain year the price of gasoline rose by $20\%$ during January, fell by $20\%$ during February, rose by $25\%$ during March, and fell by $x\%$ during April. The price of gasoline at the end of April was the same as it had been at the beginning of January. To the nearest integer, what is $x$

$\mathrm{(A)}\ 12\qquad \mathrm{(B)}\ 17\qquad \mathrm{(C)}\ 20\qquad \mathrm{(D)}\ 25\qquad \mathrm{(E)}\ 35$ -/
theorem algebra_93880 (x : ℚ) (hx : 0 < x) (h : (1 + 20 / 100) * (1 - 20 / 100) * (1 + 25 / 100) * (1 - x / 100) = 1) :
round x = 17 := by 
  -- Let $p$ be the price at the beginning of January. The price at the end of March was $(1.2)(0.8)(1.25)p = 1.2p.$ Because the price at the end of April was $p$, the price decreased by $0.2p$ during April, and the percent decrease was\[x = 100 \cdot \frac{0.2p}{1.2p} = \frac {100}{6} \approx 16.7.\]
  have al : x = 100 / 6 := by linarith
  rw [al]
  native_decide