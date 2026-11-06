import Mathlib

/-The cost of 3 hamburgers, 5 milk shakes, and 1 order of fries at a certain fast food restaurant is $\$ 23.50$. At the same restaurant, the cost of 5 hamburgers, 9 milk shakes, and 1 order of fries is $\$ 39.50$. What is the cost of 2 hamburgers, 2 milk shakes ,and 2 orders of fries at this restaurant?-/
theorem algebra_608379 (H M F : ℚ) (h1 : 3 * H + 5 * M + F = 23.5)
(h2 : 5 * H + 9 * M + F = 39.5) : 2 * H + 2 * M + 2 * F = 15 := by
-- Multiply h1 by $2$ and subtract h2, we get $H+M+F=15/2$, therefore $2* H+2* M+2*F$ is 15
  apply_fun fun t => 2 * t - 39.5 at h1; nth_rw 1 [← h2] at h1 
  ring_nf at h1; repeat rw [← mul_add]
  rw [h1]; norm_num