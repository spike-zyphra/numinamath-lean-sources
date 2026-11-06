import Mathlib

/- 
10⁷/(5*10⁴)=
(A) .002  (B) .2  (C) 20  (D) 200 (E) 2000 -/

theorem algebra_96200 : (10:ℤ)^7 / ((5:ℤ) * (10^4:ℤ)) = (200:ℤ) := by ring
--It is important to cast the numbers to be able to use ring tactic.