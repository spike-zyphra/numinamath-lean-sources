import Mathlib

/- The equation $y = -16t^2 + 80t$ describes the height (in feet) of a projectile launched from the ground at 80 feet per second. At what $t$ will the projectile reach 36 feet in height for the first time? Express your answer as a decimal rounded to the nearest tenth. -/
theorem algebra_10344 : IsLeast {t : ℝ | t ≥ 0 ∧ -16 * t ^ 2 + 80 * t = 36} 0.5 := by
  -- Solve the quadratic equation
  have H (t : ℝ) : -16 * t ^ 2 + 80 * t = 36 ↔ t = 0.5 ∨ t = 4.5 := by
    -- Two implications
    constructor <;> intro h
    . -- Solve it by contradiction
      contrapose! h
      rw [show (0.5 : ℝ) = 1 / 2 by norm_num, show (4.5 : ℝ) = 9 / 2 by norm_num] at h
      -- Use nlinarith to solve the inequality
      nlinarith (config := {splitNe := true})
    . -- Plug in the values
      obtain rfl | rfl := h
      all_goals
        norm_num

  -- Two goals
  -- 1. 0.5 is a solution
  -- 2. No other solution is less than 0.5
  constructor
  . -- 0.5 is a solution
    refine ⟨by norm_num, ?_⟩
    rw [H]
    simp
  . -- No other solution is less than 0.5
    rintro t ⟨ht, h⟩
    rw [H] at h
    -- Solutions are 0.5 and 4.5
    obtain rfl | rfl := h
    all_goals
      norm_num
