import Mathlib

theorem algebra_263842 :
    IsGreatest {z : ℕ | ∃ x y, x > 0 ∧ y > 0 ∧ x + y = 31 ∧ z = x * y} 240 := by 
  constructor
  · -- Show 240 is achievable by some x, y
    use 15, 16
    all_goals norm_num
  · -- We need to show that 240 is indeed the greatest
    intro z h
    rcases h with ⟨x, y, hx, hy, hxy, hz⟩
    have h1 : x ≤ 31 := by linarith [hxy]
    have h2 : y ≤ 31 := by linarith [hxy]
    -- Substitute z with x * y and show that x * y ≤ 240
    subst z
    -- Now we have h1 : x ≤ 31, h2 : y ≤ 31, and hxy : x + y = 31
    -- Now we need to show that x * y ≤ 240
    -- Since x + y = 31, we have y = 31 - x
    -- So x * y = x * (31 - x) = -x^2 + 31x
    -- This is a quadratic function in x that opens downward, with max at x = 15.5
    -- But x must be integer, so max at x = 15 or 16
    -- At x = 15, y = 16, x * y = 15 * 16 = 240
    -- At x = 16, y = 15, x * y = 16 * 15 = 240
    -- For all other x, 0 < x ≤ 31, y = 31 - x > 0, x * y < 240
    have h3 : y = 31 - x := by omega
    rw [h3]
    -- Now need to show that x * (31 - x) ≤ 240 
    interval_cases x <;> omega