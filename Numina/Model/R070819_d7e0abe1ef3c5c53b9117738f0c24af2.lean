import Mathlib

theorem algebra_301279 (a : ℝ) (ha : a ≠ 0) :
    ∃ x1 x2 : ℝ, x1 > 0 ∧ x2 > 0 ∧ x1 ≠ x2 ∧
      (x1^2 + a * x1 + 4 * a^2) = (3 / 2) * x1^2 ∧
      (x2^2 + a * x2 + 4 * a^2) = (5 / 2) * x2^2 := by
  by_cases h : a > 0
  · -- If $a > 0$, define $x_1$ and $x_2$ as $4a$ and $2a$ respectively
    use 4 * a, 2 * a
    constructor
    · -- Show $x_1 > 0$
      nlinarith
    constructor
    · -- Show $x_2 > 0$
      nlinarith
    constructor
    · -- Show $x_1 \neq x_2$
      intro h1
      have : a = 0 := by
        nlinarith
      contradiction
    constructor
    · -- Show first equation
      nlinarith
    · -- Show second equation
      nlinarith
  · -- Now handle the case when $a \leq 0$
    have h' : a < 0 := by
      by_contra h''
      push_neg at h''
      have : a = 0 := by
        linarith
      contradiction
    use -2 * a, (-4 * a) / 3
    constructor
    · -- Show $x_1 > 0$
      nlinarith
    constructor
    · -- Show $x_2 > 0$
      nlinarith
    constructor
    · -- Show $x_1 \neq x_2$
      intro h1
      have : a = 0 := by
        nlinarith
      contradiction
    constructor
    · -- Show first equation
      nlinarith
    · -- Show second equation
      nlinarith