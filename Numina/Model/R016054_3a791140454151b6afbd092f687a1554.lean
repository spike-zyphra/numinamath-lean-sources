import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_29822 :
  IsLeast {t : ℝ | ∃ x y z, t = x + y + z ∧ x ≥ 4 ∧ y ≥ 5 ∧ z ≥ 6 ∧ x^2 + y^2 + z^2 ≥ 90} 16 := by
  constructor
  · -- Show that 16 is in the set with the point (4,5,7)
    use 4, 5, 7
    norm_num
  · -- Show that 16 is the least element in the set
    intro t ht
    rcases ht with ⟨x, y, z, ht_eq, hx, hy, hz, h1⟩
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 5), sq_nonneg (z - 7), 
          mul_nonneg (show 0 ≤ x - 4 by linarith) (show 0 ≤ y - 5 by linarith),
          mul_nonneg (show 0 ≤ x - 4 by linarith) (show 0 ≤ z - 6 by linarith),
          mul_nonneg (show 0 ≤ y - 5 by linarith) (show 0 ≤ z - 6 by linarith)
]