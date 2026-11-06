import Mathlib

/- Solve \[\frac{5x+1}{2x^2+5x-3}=\frac{2x}{2x-1}\]for $x$.-/
theorem algebra_454 {x : ℝ} (hx : 2 * x ^ 2 + 5 * x - 3 ≠ 0 ∧ 2 * x - 1 ≠ 0) :
    (5 * x + 1) / (2 * x ^ 2 + 5 * x - 3) = 2 * x / (2 * x - 1) ↔ x = -1 := by
  -- split the proof into two cases
  constructor <;> intro h
  . -- one side: solve the equation
    -- simplify the hypothesis
    obtain ⟨h1, _⟩ := hx
    rw [(by nlinarith : (2 * x ^ 2 + 5 * x - 3) = (2 * x - 1) * (x + 3))] at h h1
    rw [mul_ne_zero_iff] at h1
    -- split the non-zero conditions
    obtain ⟨h1, h2⟩ := h1

    -- cancel 2x - 1 from the denominators
    rw [div_mul_eq_div_div_swap] at h
    rw [div_left_inj' h1] at h

    -- cross-multiply
    -- middle step
    have h3 : 5 * x + 1 = (5 * x + 1) / (x + 3) * (x + 3) := by
      symm
      exact div_mul_cancel₀ (5 * x + 1) h2
    rw [h] at h3
    -- simplify h3
    replace h3 : (x + 1) * (2 * x - 1)  = 0 := by nlinarith
    -- solve the equation
    replace h3 : x + 1 = 0 ∨ 2 * x - 1 = 0 := NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h3

    -- consider the two solutions respectively
    cases h3 with
    | inl h3 =>
      linarith -- x = -1
    | inr h3 =>
      contradiction -- x = 1/2 is an extraneous solution

  . -- the other side: x = -1 implies the equation
    rw[h]
    ring
