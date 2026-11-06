import Mathlib

theorem algebra_21192 : IsLeast {y : ℝ | y^2 = 81} (-9) := by
  constructor
  · -- Show $-9 \in \{y : \mathbb{R} \mid y^2 = 81\}$
    norm_num
  · -- Show that for all $y \in \{y : \mathbb{R} \mid y^2 = 81\}$, $-9 \leq y$
    intro y hy
    have h_eq : y^2 = 81 := by 
      simpa using hy
    nlinarith [sq_nonneg y]