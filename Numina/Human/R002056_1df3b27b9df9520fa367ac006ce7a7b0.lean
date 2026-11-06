import Mathlib

/- Suppose $a$ is a real number such that $3a + 6$ is the greatest integer less than or equal to $a$ and $4a + 9$ is the least integer greater than or equal to $a$. Compute $a$. -/
theorem inequalities_59878 (a : ℝ) (ha : ⌊a⌋ = 3 * a + 6 ∧ ⌈a⌉ = 4 * a + 9) :
    a = -3 := by
  have := ha.1
  have := ha.2
  linarith [Int.floor_le a, Int.le_ceil a]