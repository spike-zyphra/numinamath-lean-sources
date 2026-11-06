import Mathlib

/- 5. Given a pair of real numbers $(x, y)$ such that $a=2 x^{2}-y^{2}+\frac{3}{2}$ and $b=y^{4}+4 x+2$ have a maximum value not exceeding 1, then the range of $(x, y)$ that satisfies the condition is $\qquad$ . -/
theorem algebra_172638 (x y : ℝ) (a b : ℝ) (ha : a = 2 * x ^ 2 - y ^ 2 + 3 / 2) (hb : b = y ^ 4 + 4 * x + 2):
    a ≤ 1 ∧ b ≤ 1 ↔
    (x = -1 / 2 ∧ y = 1) ∨ (x = -1 / 2 ∧ y = -1) := by
  constructor
  -- first proving the x, y values, we can add up the inequalities to get sum of two squares ≤ 0
  . rintro ⟨ha', hb'⟩
    have : (2 * x + 1)^2 + (y^2 - 1)^2 ≤ 0 := by linarith
    have : 0 ≤ (2 * x + 1)^2 := by positivity
    have : 0 ≤ (y^2 - 1)^2 := by positivity
    -- so the squares are zero, in particular 2x + 1 = 0 and y^2 - 1 = 0, from this we get our results
    have : (2 * x + 1)^2 = 0 := by linarith
    simp at this
    simp [show x = - 1 / 2 by linarith]
    have : (y^2 - 1)^2 = 0 := by linarith
    simp at this
    rwa [sub_eq_zero, sq_eq_one_iff] at this
  -- other direction just plug in and compute
  . rintro h
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> rw [ha, hb] <;> norm_num