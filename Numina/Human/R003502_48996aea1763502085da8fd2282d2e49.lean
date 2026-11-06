import Mathlib

/- 32. If $x, y$, and $z$ are real numbers such that $2 x^{2}+y^{2}+z^{2}=2 x-4 y+2 x z-5$, find the maximum possible value of $x-y+z$. -/
theorem algebra_188862 : IsGreatest {a : ℝ | ∃ x y z, a = x - y + z ∧ 2 * x ^ 2 + y ^ 2 + z ^ 2 = 2 * x - 4 * y + 2 * x * z - 5} 4 := by
  apply And.intro
  · -- 4 is in the given set, so if it is an upperbound then it is the maximum of the given set.
    show ∃ x y z, 4 = x - y + z ∧ 2 * x ^ 2 + y ^ 2 + z ^ 2 = 2 * x - 4 * y + 2 * x * z - 5
    use 1, -2, 1
    ring_nf
    simp
  · simp [upperBounds]
    show ∀ a x y z,  a = x - y + z → 2 * x ^ 2 + y ^ 2 + z ^ 2 = 2 * x - 4 * y + 2 * x * z - 5 → a ≤ 4
    rintro a x y z rfl h
    -- The equation rearranges as $(x - 1) ^ 2 + (y + 2) ^ 2 + (x - z) ^ 2 = 0$, so we must have $x = 1$, $y = -2$, $z = -1$, giving us 4
    have : (x - 1) ^ 2 + (y + 2) ^ 2 + (x - z) ^ 2 = 0 := by nlinarith
    have : x = 1 := by nlinarith
    have : y = -2 := by nlinarith
    have : z = 1 := by nlinarith
    linarith