import Mathlib
/- Find all real numbers $x, y$ such that

$$
x(x-2 y)+y(2 y-4)+4=0
$$ -/
theorem algebra_607355 {x y : ℝ} : x * (x - 2 * y) + y * (2 * y - 4) + 4 = 0 ↔ x = 2 ∧ y = 2 := by
    constructor
    . -- Forward direction: proving that the equation implies x = 2 and y = 2
        intro h
        -- Rearrange the equation into sum of two squares: (x-y)² + (y-2)² = 0
        replace h : (x - y) ^ 2 + (y - 2) ^ 2 = 0:= by linarith
        -- Use the fact that squares of real numbers are non-negative
        have h1 : (x - y) ^ 2 ≥ 0:= by positivity
        have h2 : (y - 2) ^ 2 ≥ 0:= by positivity
        -- Since sum of two non-negative numbers is zero, both must be zero
        replace h1 : (x - y) ^ 2 = 0:= by linarith
        replace h2 : (y - 2) ^ 2 = 0:= by linarith
        -- If square is zero, the number itself must be zero
        replace h1 : x - y = 0:= by exact pow_eq_zero h1
        replace h2 : y - 2 = 0:= by exact pow_eq_zero h2
        constructor
        all_goals
        -- Solve the linear equations to get x = 2 and y = 2
        linarith
    . -- Backward direction: proving that x = 2 and y = 2 satisfies the equation
        intro h
        rcases h with ⟨h1, h2⟩
        -- Substitute x = 2 and y = 2
        subst x y
        -- Verify the equation holds
        linarith
