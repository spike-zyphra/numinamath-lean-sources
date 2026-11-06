import Mathlib

/- Find the minimum value of $x^6 + y^6 - 54xy$ over all real numbers $x$ and $y.$ -/
theorem algebra_21422 :
    IsLeast {z : ℝ | ∃ x y, z = x^6 + y^6 - 54 * x * y} (-108) := by
  -- Two goals to prove
  -- 1. The value 1-108 is attainable
  -- 2. The value -108 is the minimum
  constructor
  . -- First goal
    -- Set x = y = √3
    use √3, √3
    have h : √3^2 = 3 := by simp
    -- We can get the desired equation from the fact that √3^2 = 3
    linear_combination (-(2 * √3 ^ 4) - 6 * √3 ^ 2 + 36) * h
  . -- Second goal
    -- We prove that x^6 + y^6 - 54xy ≥ -108
    rintro z ⟨x, y, rfl⟩
    -- Without loss of generality, assume x * y ≥ 0
    wlog h : x * y ≥ 0 with H
    {
        -- If otherwise, we can set y = -y
        push_neg at h
        specialize H x (-y) (by linarith)
        -- x ^ 6 + y ^ 6 - 54 * x * y ≥ x ^ 6 + (-y) ^ 6 - 54 * x * (-y) ≥ -108
        linarith
    }
    -- Use x^6 + y^6 ≥ 2 * (x * y) ^ 3 (AM-GM inequality)
    calc x^6 + y^6 - 54 * x * y ≥ 2 * (x * y) ^ 3 - 54 * (x * y) := by linarith only [sq_nonneg (x^3 - y^3)]
         _ ≥ _ := ?_
    -- Let t = x * y
    generalize k : x * y = t at h ⊢
    clear k x y
    -- The equation becomes 2 * t^3 - 54 * t ≥ -108
    -- Which is equivalent to 2 * (t - 3)^2 * (t + 6) ≥ 0
    nlinarith [sq_nonneg (t - 3)]
