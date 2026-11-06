import Mathlib

theorem algebra_257854 (f : ℝ → ℝ) (hf : f = fun x => 2007 * x ^ 3 + 2006 * x ^ 2 + 2005 * x) :
    (∃! x, f x = 0) := by
  use 0
  constructor
  · -- Show that 0 is indeed a root.
    simp [hf]
  · -- Show that if another root exists, it must be equal to 0.
    intro x
    simp [hf]
    intro hx
    -- Assume $2007 * x^3 + 2006 * x^2 + 2005 * x = 0$, prove $x = 0$
    have h_eq : 2007 * x^3 + 2006 * x^2 + 2005 * x = 0 := by
      linarith
    have h_eq2 : x * (2007 * x^2 + 2006 * x + 2005) = 0 := by
      linarith [h_eq]
    cases' (mul_eq_zero.mp h_eq2) with hx1 hx2
    · -- Case where x = 0
      linarith
    · -- Case where 2007 * x^2 + 2006 * x + 2005 = 0
      have h1 : 2007 * x^2 + 2006 * x + 2005 = 0 := by
        linarith
      nlinarith [sq_nonneg (x * 2007 + 2006 / 2), sq_nonneg (x + 1003 / 2007), sq_nonneg (x - (-2006 / (2 * 2007)))]