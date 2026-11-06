import Mathlib

/- Four friends do yardwork for their neighbors over the weekend, earning $15, $20, $25 and $40 respectively.
They decide to split their earnings equally among themselves. In total, how much will the friend who earned $40 give to the others? 
(A) $5 (B)$10 (C) $15 (D) $20 (E)$25 -/ 
theorem algebra_94058 (total : ℝ) (h : total = 15 + 20 + 25 + 40) : (40 - total / 4) = 15 := by
--the fourth friend earning $40, will give away the difference he has from the arithmetic mean 
rw [h]; norm_num