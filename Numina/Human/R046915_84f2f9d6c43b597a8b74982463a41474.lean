import Mathlib

/- Suppose that $x, y$, and $z$ are non-negative real numbers such that $x+y+z=1$. What is the maximum possible value of $x+y^{2}+z^{3}$ ?-/
theorem algebra_608668 :
    IsGreatest {w | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = 1 ∧ w = x + y ^ 2 + z ^ 3} 1 := by
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- First show that the value 1 is possible.
    use 1, by norm_num, 0, by rfl, 0, by rfl
    norm_num
  . -- Next show that 1 is the largest possible value.
    intro w x hx y hy z hz h₀ h₁
    rw [h₁]
    calc
      x + y ^ 2 + z ^ 3 ≤ x + y + z := by
        apply add_le_add
        apply add_le_add_left
        . -- We have y ^ 2 ≤ y because y ≤ 1.
          nlinarith
        . -- We have z ^ 3 ≤ z because z ≤ 1.
          nlinarith [show z ^ 2 ≤ 1 by nlinarith]
      _ = 1 := h₀