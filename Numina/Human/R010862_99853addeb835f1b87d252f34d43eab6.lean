import Mathlib

open Real

/- 14. Let $ f(x) = A(x^2 - 2x)e^x - e^x + 1 $. For any $ x \leq 0 $, $ f(x) \geq 0 $ holds. Determine the range of the real number $ A $. -/
theorem algebra_202329 (A : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = A * (x ^ 2 - 2 * x) * exp x - exp x + 1) :
    (∀ x ≤ 0, f x ≥ 0) ↔ A ≥ -1 / 2 := by
  have hf' : f = fun x => f x := by ext x; simp
  -- Compute the derivative of f:
  -- f'(x) = (A * x^2 - (2 * A + 1)) * exp x.
  have hdf x : HasDerivAt f ((A * x^2 - (2 * A + 1)) * exp x) x := by
    rw [hf', show (A * x^2 - (2 * A + 1)) * exp x = A * (2 * x ^ 1 - 2 * 1) * exp x + A * (x^2 - 2 * x) * exp x - exp x by ring]
    simp_rw [hf]
    apply HasDerivAt.add_const
    apply HasDerivAt.sub _ (hasDerivAt_exp _)
    apply HasDerivAt.mul _ (hasDerivAt_exp _)
    apply HasDerivAt.const_mul
    apply HasDerivAt.sub (hasDerivAt_pow _ _)
    apply HasDerivAt.const_mul
    exact hasDerivAt_id' x
  -- We have f(0) = 0.
  have hf0 : f 0 = 0 := by simp [hf]
  constructor
  · intro hf1
    -- Show that if f(x) ≥ 0 for all x ≤ 0, then A ≥ -1 / 2.
    -- Assume that A < -1 / 2 and find x ≤ 0 such that f(x) < 0.
    contrapose! hf1
    -- Let x = -√((2 * A + 1) / A).
    let x := -√((2 * A + 1) / A)
    -- We have x < 0 (since 2 * A + 1 < 0 and A < 0).
    have hx0 : x < 0 := by
      simp [x]
      apply div_pos_of_neg_of_neg (by linarith) (by linarith)
    use x, le_of_lt hx0
    -- Show that f(x) < f(0) = 0.
    rw [← hf0]
    -- It is enough to show that the derivative of f(x) is positive on (x, 0).
    apply strictMonoOn_of_deriv_pos (convex_Icc x 0) _ _ (by simp; linarith) (by simp; linarith) hx0
    · apply HasDerivAt.continuousOn
      intro x hx
      apply hdf
    simp only [interior_Icc, Set.mem_Ioo, and_imp]
    intro t ht1 ht2
    rw [(hdf t).deriv]
    -- exp(t) > 0 for all t so we need to show that A * t^2 - (2 * A + 1) < 0
    -- for t ∈ (x, 0).
    apply mul_pos _ (by positivity)
    rw [sub_pos]
    calc
      -- We have 2 * A + 1 = A * x^2 (from the definition of x).
      2 * A + 1 = A * x ^ 2 := by
        simp [x]
        rw [sq_sqrt (div_nonneg_of_nonpos (by linarith) (by linarith))]
        field_simp [show A ≠ 0 by linarith]
      -- A < 0 and t ∈ (x, 0) imply that A * x^2 < A * t^2.
      _ < A * t ^ 2 := by
        apply mul_lt_mul_of_neg_left _ (by linarith)
        rw [sq_lt_sq, abs_of_neg ht2, abs_of_neg hx0]
        linarith
  · intro ha x hx
    -- Assume that A ≥ -1/2 and show that f(x) ≥ 0 for all x ≤ 0.
    -- Consider two cases: 0 ≤ A and A < 0.
    by_cases ha2 : 0 ≤ A
    · rw [hf, show A * (x^2 - 2 * x) * exp x - exp x + 1 = (A * exp x) * (x * (x - 2)) + (1 - exp x) by ring]
      -- If 0 ≤ A then f(x) = A * exp(x) * (x * (x - 2)) + (1 - exp(x)) ≥ 0 because
      -- A * exp(x) ≥ 0, x * (x - 2) > 0 (since x ≤ 0 implies x - 2 ≤ 0), and
      -- 1 - exp(x) ≥ 0 since exp(x) ≤ 1 for all x ≤ 0.
      apply add_nonneg
      · apply mul_nonneg (by positivity)
        nlinarith
      · rw [sub_nonneg, exp_le_one_iff]
        exact hx
    -- Assume now that -1/2 ≤ A < 0.
    -- We need to show that f(x) ≥ f(0) = 0 for x ≤ 0.
    rw [← hf0]
    -- Show that f(x) is a decreasing function.
    -- It is enough to show that the derivative of f is nonpositive.
    apply antitone_of_deriv_nonpos _ _ hx
    · intro x
      exact (hdf x).differentiableAt
    intro x
    rw [(hdf x).deriv]
    -- We have exp(x) > 0 for all x so we need to show that
    -- A * x^2 - (2 * A + 1) ≤ 0 for all x.
    apply mul_nonpos_of_nonpos_of_nonneg _ (by positivity)
    -- -1/2 ≤ A < 0 implies that -(2 * A + 1) < 0 and A * x^2 ≤ 0.
    nlinarith