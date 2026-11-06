import Mathlib

/- Given that the complex number $(a^{2}-3a+2)+(a-2)i$ is a pure imaginary number, find the value of the real number $a$.-/
theorem algebra_9318 {a : ℝ} {z : ℂ} (hz : z = (a ^ 2 - 3 * a + 2) + (a - 2) * .I)
    (hzre : z.re = 0) (hzim : z.im ≠ 0) :
    a = 1 := by
  -- Since z is a pure imaginary number, we have $a^2-3a+2=0$ and
  simp [hz, pow_two] at hzre
  -- $a-2≠0$.
  simp [hz, pow_two, -ne_eq] at hzim
  -- Simplify $a^2-3a+2=0$ to $(a-2)(a-1)=0$.
  replace hzre : (a - 2) * (a - 1) = 0 := by linear_combination hzre
  rw [mul_eq_zero] at hzre
  rcases hzre with h | h
  -- If a = 2, then there is a contradiction.
  . contradiction
  -- a=1 is desired conclusion.
  linear_combination h
