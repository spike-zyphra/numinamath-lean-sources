import Mathlib

/- Solve the system of equations:

$$
\left\{\begin{array}{l}
x^{5}=y+y^{5} \\
y^{5}=z+z^{5} \\
z^{5}=t+t^{5} \\
t^{5}=x+x^{5} .
\end{array}\right.
$$ -/
theorem algebra_240565 :
    {(x, y, z, t) : ℝ × ℝ × ℝ × ℝ | x ^ 5 = y + y ^ 5 ∧ y ^ 5 = z + z ^ 5 ∧ z ^ 5 = t + t ^ 5 ∧ t ^ 5 = x + x ^ 5} = {(0, 0, 0, 0)} := by
  -- The only solution is (0, 0, 0, 0)
  ext ⟨x, y, z, t⟩
  simp
  constructor
  -- We quickly check that (0, 0, 0, 0) is a solution
  swap
  {
    rintro ⟨rfl, rfl, rfl, rfl⟩
    simp
  }
  -- We now show that (0, 0, 0, 0) is the only solution
  rintro ⟨h₁, h₂, h₃, h₄⟩
  -- By adding up all the equations, we get that x + y + z + t = 0
  have H : x + y + z + t = 0 := by linear_combination -(h₁ + h₂ + h₃ + h₄)
  -- We only need to show that x = 0, the rest follows immediately
  suffices hx : x = 0 by
    subst x
    simp at h₄
    subst t
    simp at h₃
    subst z
    simp at h₂
    subst y
    simp at h₁
    simp
  -- If x ≠ 0, then we can assume that x > 0 without loss of generality
  by_contra! hx'
  wlog hx : 0 < x with K
  {
    -- If x > 0 does not hold, then x < 0, and we can apply the hypothesis to -x, -y, -z, -t
    simp at hx
    apply lt_of_le_of_ne hx at hx'
    apply K (-x) (-y) (-z) (-t)
    all_goals
      linarith
  }
  -- We have t ^ 5 > 0, so t > 0
  have ht : 0 < t^5 := by rw [h₄]; positivity
  rw [Odd.pow_pos_iff (show Odd 5 by decide)] at ht
  -- We have z ^ 5 > 0, so z > 0
  have hz : 0 < z^5 := by rw [h₃]; positivity
  rw [Odd.pow_pos_iff (show Odd 5 by decide)] at hz
  -- We have y ^ 5 > 0, so y > 0
  have hy : 0 < y^5 := by rw [h₂]; positivity
  rw [Odd.pow_pos_iff (show Odd 5 by decide)] at hy
  linarith
