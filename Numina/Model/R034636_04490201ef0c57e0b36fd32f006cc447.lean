import Mathlib

open Real Set

theorem inequalities_3534 {a : ℝ} (ha : a^3 < a ∧ a < a^2) :
    {x | x + a > 1 - a * x} = {x | x < (1 - a) / (1 + a)} := by

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume x + a > 1 - a * x; prove x < (1 - a) / (1 + a)
    intro h
    have h1 : a ^ 3 < a := ha.1
    have h2 : a < a ^ 2 := ha.2
    -- From `a < a ^ 2` it is `a * (a - 1) > 0` which means either a > 1 or a < 0
    -- From `a^3 < a` it is `a * (a^2 - 1) < 0` which means either -1 < a < 0 or a > 1
    have h3 : a < -1 := by
      nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a), h1, h2]

    have h4 : 1 + a < 0 := by linarith

    have h5 : x * (1 + a) > 1 - a := by
      nlinarith

    have h6 : x < (1 - a) / (1 + a) := by
      apply (lt_div_iff_of_neg' (by linarith)).mpr
      nlinarith

    exact h6
  · -- Assume x < (1 - a) / (1 + a); prove x + a > 1 - a * x
    intro h
    have h1 : a ^ 3 < a := ha.1
    have h2 : a < a ^ 2 := ha.2
    have h3 : a < -1 := by
      nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a), h1, h2]

    have h4 : 1 + a < 0 := by linarith

    have h5 : x * (1 + a) > 1 - a := by
      have h6 : x < (1 - a) / (1 + a) := h
      apply (lt_div_iff_of_neg' (by linarith)).mp at h6
      nlinarith

    nlinarith