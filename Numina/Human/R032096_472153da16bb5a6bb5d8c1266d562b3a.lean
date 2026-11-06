import Mathlib

/- The height of a ball when it is thrown off a cliff can be represented by the equation $h=45-7t-6t^2$, where $t$ is time in seconds. In how many seconds will the ball reach a height of 25 feet? -/
theorem algebra_758 (h : ℝ → ℝ) (ht : h = fun t => 45 - 7 * t - 6 * t ^ 2) :
    0 ≤ t ∧ h t = 25 ↔ t = 4 / 3 := by

  constructor

  -- Direction 1: If 0 ≤ t and h(t) = 25, then t = 4/3.
  · intro ⟨hl, hr⟩
    -- Substitute the function definition into hr.
    have h2 : 6 * t * t + 7 * t + (-20) = 0 := by
      rw [ht] at hr
      simp_all
      linarith

    -- The coefficient 6 is non-zero.
    have ha : (6 : ℝ) ≠ 0 := by linarith

    -- Calculate the discriminant of the quadratic equation.
    have h' : discrim (6 : ℝ) 7 (-20) = 23 * 23 := by
      simp [discrim]
      linarith

    -- Use the quadratic formula to solve the equation.
    rw [mul_assoc, quadratic_eq_zero_iff ha h'] at h2
    cases h2 with
    | inl h3 =>
      -- The first solution is t = 4/3.
      rw [h3]
      norm_num
    | inr h4 =>
      -- The second solution is t = -5/2, which contradicts 0 ≤ t.
      have h5 : t = - 5 / 2 := by
        calc
        t = (-7 - 23) / (2 * 6) := by simp [h4]
        _ = - 5 / 2 := by ring
      rw [h5] at hl
      nlinarith

  -- Direction 2: If t = 4/3, then 0 ≤ t and h(t) = 25.
  · intro h1
    -- 4/3 is non-negative.
    have h2 : (0:ℝ) ≤ 4 / 3 := by norm_num

    -- Calculate h(4/3) using the function definition.
    have h3 : h (4 / 3) = 25 := by
      rw [ht]
      simp
      norm_num

    rw [← h1] at h2 h3
    exact ⟨h2, h3⟩
