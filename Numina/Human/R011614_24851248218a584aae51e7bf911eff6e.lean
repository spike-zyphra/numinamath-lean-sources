import Mathlib

/- # 4. CONDITION

Let $a, b, c$ and $d$ be real numbers such that for all real values of $x$, the equality $|2 x+4|+|a x+b|$ $=|c x+d|$ holds. Prove that $d=2 c$. -/
theorem algebra_135494 (a b c d : ℝ)
    (h : ∀ x : ℝ, |2 * x + 4| + |a * x + b| = |c * x + d|) :
    d = 2 * c := by
  -- We first show that `c ≠ 0`.
  have hc : c ≠ 0 := by
    -- If `c = 0`, then the equality becomes `|2 * x + 4| + |a * x + b| = |d|`.
    rintro rfl
    -- We set `x := |d|` in the equality.
    specialize h |d|
    -- LHS ≥ 2 * |d| + 4 > |d| = RHS, contradiction
    simp [abs_of_nonneg, show 2 * |d| + 4 ≥ 0 by positivity] at h
    linarith [abs_nonneg d, abs_nonneg (a * |d| + b)]
  -- Let's set `x := -d / c` in the equality.
  specialize h (-d / c)
  simp [mul_div_cancel₀, hc] at h
  -- So we have `|2 * (-d / c) + 4| + |a * (-d / c) + b| = 0`.
  -- By positivity of absolute value, we have `2 * (-d / c) + 4 = 0`.
  have h₁ : 2 * (-d / c) + 4 = 0 := by
    rw [← abs_eq_zero]
    linarith [abs_nonneg (2 * (-d / c) + 4), abs_nonneg (a * (-d / c) + b)]
  -- And we are done.
  field_simp at h₁
  linarith only [h₁]
