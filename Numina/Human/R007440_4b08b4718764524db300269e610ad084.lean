import Mathlib

/- The function $f$ is not defined for $x = 0,$ but for all non-zero real numbers $x,$
\[f(x) + 2f \left( \frac{1}{x} \right) = 3x.\]Find the real solutions to $f(x) = f(-x).$  Enter the real solutions, separated by commas. -/
theorem algebra_12592 {f : ℝ → ℝ} (hf : ∀ {x}, x ≠ 0 → f x + 2 * f (1 / x) = 3 * x) : {x | x ≠ 0 ∧ f x = f (-x)} = {√2, -√2} := by

  -- We have f x = (2 - x^2) / x for all x ≠ 0
  have H {x} (hx : x ≠ 0) : f x = (2 - x ^ 2) / x := by
    -- Plug in x and 1 / x into the equation hf
    have h1 := hf hx
    have h2 := hf (show 1 / x ≠ 0 from one_div_ne_zero hx)
    -- Simplify h2
    rw [show 1 / (1 / x) = x by simp] at h2
    -- Simplify the goal
    rw [show (2 - x ^ 2) / x = 2 * (1 / x) - x by field_simp; ring]
    -- Solve the linear equations
    linarith

  ext x
  simp
  -- Two goals:
  -- 1. Show that f x = f (-x) (x ≠ 0) implies x = √2 or x = -√2
  -- 2. Show that x = √2 or x = -√2 implies f x = f (-x) (x ≠ 0)
  constructor
  . -- Goal 1
    rintro ⟨h1, h2⟩
    -- Use the lemma H to eliminate f
    rw [H h1, H (show -x ≠ 0 from mt neg_eq_zero.1 h1)] at h2
    simp [div_neg] at h2
    replace h2 : (2 - x ^ 2) / x = 0 := by linarith only [h2]
    simp [h1] at h2
    -- After simplification, 2 - x^2 = 0
    rw [← sq_eq_sq_iff_eq_or_eq_neg]
    simp
    linarith only [h2]

  . -- Goal 2
    -- Just plug in x = √2 or x = -√2 into the equation H
    rintro (rfl | rfl)
    . simp [H]
    . simp [H]
