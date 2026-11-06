import Mathlib
open Real

/- To m ounces of a m% solution of acid,  ounces of water are added to yield a
(m - 10)% solution. If m > 25, then α is
(A）10m/(m-10) (B) 5m/(m-10) (C) m/(m-10)  (D) 5m/(m-20)
(E) not determined by the given information -/
theorem algebra_95412 {m x : ℝ} (hm : m > 25) (hx : x > 0)
(h : m*(m/100)/(m+x)=(m-10)/100) :
x = 10 * m / (m - 10) := by
  -- solve by rearranging and eliminating the terms
  field_simp [(by linarith:m-10≠0)] at *
  linarith