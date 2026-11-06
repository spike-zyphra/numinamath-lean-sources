import Mathlib

/- At a certain amusement park, there is a bulk discount for tickets. If you buy up to 60 tickets in one order, the price for each ticket is $\$70$. However if you buy more than 60 tickets in a single order, the price of every ticket is reduced by $\$1$ for each additional ticket bought. If $t$ is the number of tickets bought in bulk at one time, what is the largest $t$ which will bring the amusement park a profit greater than $\$4200$? -/
theorem algebra_18913 : IsGreatest {t : ℤ | t > 60 ∧ 70 * t - (t - 60) * t > 4200} 69 := by
  constructor
  -- $69$ satisfies the property
  norm_num
  -- if $t$ satisfies the property, then $t \leq 69$
  intro t h
  simp only [gt_iff_lt, Set.mem_setOf_eq] at h
  have h1 : t ^ 2 - 130 * t + 4200 < 0 := by
    linarith
  have h2 : t ^ 2 - 130 * t + 4200 = (t - 60) * (t - 70) := by
    ring
  rw [h2] at h1
  have h3 : t - 60 > 0 := by
    linarith
  have h4 : t - 70 < 0 := by
    exact (pos_iff_neg_of_mul_neg h1).mp h3
  linarith