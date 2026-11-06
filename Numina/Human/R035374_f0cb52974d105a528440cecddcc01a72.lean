import Mathlib

/- 6. (6 points) Fill in a natural number in each of the $\square$ and $\triangle$ to make the equation true.
$$
\square^{2}+12=\triangle^{2} \text {, then: } \square+\triangle=6 \text {. }
$$-/
theorem algebra_251576 {x y : ℕ} (h : x ^ 2 + 12 = y ^ 2) :
    x + y = 6 := by
  -- Show that x ≤ 6.
  have hx : x ≤ 6 := by
    by_contra!
    -- Assume on the contrary that x > 6, then there is not enough gap between x² and y².
    have : x < y := by
      nlinarith
    have : y < x + 1 := by
      nlinarith
    omega
  -- Show that y ≤ 6.
  have hy : y ≤ 6 := by
    nlinarith
  -- For each case of x, y, close the goal with omega.
  interval_cases x
  <;> interval_cases y
    <;> omega