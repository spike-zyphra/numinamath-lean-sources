import Mathlib

open Real Set
open scoped BigOperators

/- What is the range of the function $$F(x) = |x+1|+|x-5|~?$$Express your answer in interval notation. -/
theorem algebra_21803 (F : ℝ → ℝ) (hF : F = λ x => abs (x + 1) + abs (x - 5)) :
    range F = Ici 6 := by
    -- simplify the expression
    simp [range]
    -- introduce x
    ext x
    rw [hF]
    simp
    -- split the goal into two
    constructor <;> intro h
    .   -- prove that x ≥ 6
        -- introduce y
        rcases h with ⟨y, h⟩
        by_cases hy : y < -1
        .   -- case 1: y < -1
            -- use the property of abs
            repeat rw [abs_of_neg (by linarith)] at h
            -- trivial calculation
            linarith
        .   -- discuss the relationship between y and 5
            by_cases hy' : y < 5
            .   -- case 2: -1 ≤ y < 5
                rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at h
                linarith
            .   -- case 3: y ≥ 5
                repeat rw [abs_of_nonneg (by linarith)] at h
                linarith
    .   -- prove that any x ≥ 6 is in the range
        -- y = (x + 4) / 2 satisfies the equation
        use (x + 4) / 2
        -- similar calculation
        repeat rw [abs_of_nonneg (by linarith)]
        linarith
