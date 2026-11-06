import Mathlib

/- Given $x > 0$, $y > 0$, and $9x + y = xy$, find the minimum value of the positive real number $a$ such that the inequality $ax + y \geq 25$ holds for all positive real numbers $x$, $y$. -/
theorem algebra_9387 :
    IsLeast {a | 0 < a ∧ (∀ x y : ℝ, x > 0 → y > 0 → 9 * x + y = x * y → a * x + y ≥ 25)} 4 := by

  -- We have two goals:
  -- 1. Prove that 4 satisfies the condition
  -- 2. Prove that no smaller positive real number satisfies the condition
  simp [IsLeast, lowerBounds]
  constructor

  . -- Prove that 4 satisfies the condition
    intro x y hx hy h
    -- We have 1 / x + 9 / y = 1 from the given equation
    replace h : 1 / x + 9 / y = 1 := by
      field_simp
      linarith

    -- AM-GM inequality
    have AMGM {a b} (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b ≥ 2 * √(a * b) := by
      have h : 0 ≤ (√a - √b) ^ 2 := sq_nonneg _
      simp [sub_sq, ha, hb] at h
      simp [Real.sqrt_mul ha]
      linarith

    -- 4x + y = (4x + y) * (1 / x + 9 / y) = 13 + 36x / y + y / x ≥ 13 + 2 * √(36x / y * y / x) = 25
    calc 4 * x + y = (4 * x + y) * (1 / x + 9 / y) := by rw [h]; ring
                _ = 13 + 36 * x / y + y / x := by field_simp; ring
                _ ≥ 13 + 2 * √((36 * x / y) * (y / x)) := by linarith [AMGM (by positivity : 36 * x / y ≥ 0) (by positivity : y / x ≥ 0)]
                _ = 13 + 2 * √(6 ^ 2) := by rw [(by field_simp; ring : (36 * x / y) * (y / x) = 6 ^ 2)]
                _ = 25 := by simp; norm_num

  . -- Prove that no smaller positive real number satisfies the condition
    intro a _ h
    -- Choose x = 5/2, y = 15
    specialize h (5 / 2) 15 (by norm_num) (by norm_num) (by linarith)
    linarith
