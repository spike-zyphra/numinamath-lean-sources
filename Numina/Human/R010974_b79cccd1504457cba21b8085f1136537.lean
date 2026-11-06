import Mathlib

/- ## Problem 12

Given unequal integers $x, y, z$ prove that $(x-y)^{5}+(y-z)^{5}+(z-x)^{5}$ is divisible by $5(x-y)(y-z)(z - x)$.

 -/
theorem algebra_206233 {x y z : ℤ} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    5 * (x - y) * (y - z) * (z - x) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by
    -- Let $r = x - y$ and $s = y - z$
    let r := x - y
    let s := y - z
    -- The left-hand-side can be rewritten as $- 5 * r * s * (r + s)$
    have h1 : 5 * (x - y) * (y - z) * (z - x) = - 5 * r * s * (r + s) := by
      simp [r, s]
      nlinarith
    /- For the right-hand-side we have
       $$(x - y)^5 + (y - z)^5 + (z - x)^5 = r^5 + s^5 - (r + s) ^ 5 = -5r^4s -10r^3s^2 - 10r^2s^3 - 5rs^4 = - 5 * r * s * (r + s) * (r ^2 + r * s + s^2),$$ -/
    have h2 : (x - y)^5 + (y - z)^5 + (z - x)^5 = (- 5 * r * s * (r + s)) * (r ^2 + r * s + s^2) := by
      simp [r,s]
      nlinarith
    rw [h1, h2]
    -- Clearly the left-hand-side is a divisor of the right-hand-side
    use r ^2 + r * s + s^2