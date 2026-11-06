import Mathlib


/- What is the greatest possible value of $a$ in the system of equations $5a + 2b = 0$ and $ab = -10$? -/
theorem algebra_21688 :
    IsGreatest {a : ℝ | ∃ b, 5 * a + 2 * b = 0 ∧ a * b = -10} 2 := by

  -- a can be -2 or 2
  have h_possible_a {a b : ℝ} : (5 * a + 2 * b = 0 ∧ a * b = -10) → (a = -2 ∨ a = 2) := by
    intro ⟨h1, h2⟩

    -- by adding the two equations, $ab + 5a + 2b = -10 \Longrightarrow ab + 5a + 2b + 10 = 0$.
    have h : a * b + 5 * a + 2 * b + 10 = 0 := by
      linear_combination (h1 + h2)

    -- This factors! Thus, $(a+2)(b+5) = 0$,
    replace h : (a + 2) * (b + 5) = 0 := by
      convert h using 1
      ring

    -- from which it follows that at least one of the two statements $a = -2$, $b = -5$ is true.
    rcases mul_eq_zero.mp h with h | h
    . simp [eq_neg_of_add_eq_zero_left h]
    -- In the latter case, we obtain $a = \boxed{2}$,
    . apply eq_neg_of_add_eq_zero_left at h
      apply_fun fun t => t * b⁻¹ at h2
      rw [mul_inv_cancel_right₀ (by linarith only [h]), h] at h2
      norm_num at h2
      simp [h2]

  dsimp [IsGreatest]
  constructor

  -- 2 is reachable
  . use -5
    norm_num

  -- 2 is upperBound
  . apply mem_upperBounds.mpr
    intro a h
    obtain ⟨b, h⟩ := h
    rcases h_possible_a h
    <;> linarith