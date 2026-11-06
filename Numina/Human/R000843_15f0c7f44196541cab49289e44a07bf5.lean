import Mathlib

/- Lines $y=(3a+2)x-2$ and $2y=(a-4)x+2$ are parallel. What is the value of $a$? -/
theorem algebra_18544 {a : ℝ} (h : ∀ x y, ¬(y = (3 * a + 2) * x - 2 ∧ 2 * y = (a - 4) * x + 2))  :
    a = -8 / 5 := by
  by_contra contra
  -- if $a \neq -8 / 5$ then $(6 / (5a + 8), (8a - 4) / (5a + 8))$ is the intersection point of the two lines
  have ne : 5 * a + 8 ≠ 0 := by
    by_contra contra1
    have aeq : a = -8 / 5 := by
      linarith
    contradiction
  let x : ℝ := 6 / (5 * a + 8)
  let y : ℝ := (8 * a - 4) / (5 * a + 8)
  have intersect : y = (3 * a + 2) * x - 2 ∧ 2 * y = (a - 4) * x + 2 := by
    dsimp [x, y]
    field_simp
    ring_nf
    simp only [and_self]
  have noninter := h x y
  contradiction