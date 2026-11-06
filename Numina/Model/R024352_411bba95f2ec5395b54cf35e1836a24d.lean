import Mathlib

theorem algebra_309086 {x a : ℝ} (hx : x > 0) (ha : a ≠ 0)
    (h1 : Real.sqrt x = (1 - a) / 2) (h2 : Real.sqrt (x + a) - Real.sqrt (x - a + 2) = -2) :
    a ≤ -1 := by

  have h3 : (1 - a) / 2 ≥ 0 := by
    have h31 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
    linarith [h1, h31]

  -- From h3, we get $a \leq 1$.
  have h4 : a ≤ 1 := by
    linarith [h3]

  have h6 : Real.sqrt (x + a) = Real.sqrt (x - a + 2) - 2 := by
    linarith

  have h7 : Real.sqrt (x + a) ≥ 0 := by
    apply Real.sqrt_nonneg

  -- From h6 and h7, derive that right side must be non-negative.
  have h8 : Real.sqrt (x - a + 2) - 2 ≥ 0 := by
    nlinarith [h6, h7]

  -- So Real.sqrt (x - a + 2) ≥ 2.
  have h9 : Real.sqrt (x - a + 2) ≥ 2 := by
    nlinarith

  have h131 : x - a + 2 ≥ 0 := by
    by_contra h
    push_neg at h
    -- If x - a + 2 < 0, then sqrt(x - a + 2) = 0.
    have h132 : Real.sqrt (x - a + 2) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals linarith
    nlinarith [h9, h132]

  -- From Real.sqrt (x - a + 2) ≥ 2, square both sides to get x - a + 2 ≥ 4.
  have h10 : x - a + 2 ≥ 4 := by
    have h11 : (Real.sqrt (x - a + 2)) ^ 2 ≥ (2 : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - a + 2), h9]
    have h12 : (Real.sqrt (x - a + 2)) ^ 2 = x - a + 2 := by
      rw [Real.sq_sqrt]
      linarith [h131]
    nlinarith [h12, h11]

  -- So x - a ≥ 2.
  have h15 : x - a ≥ 2 := by
    linarith

  -- From the first equation: x = ((1 - a) / 2) ^ 2.
  have h5 : x = ((1 - a) / 2) ^ 2 := by
    calc
      x = (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = ((1 - a) / 2) ^ 2 := by
        rw [h1]

  -- Substitute x in x - a ≥ 2.
  have h16 : ((1 - a) / 2) ^ 2 - a ≥ 2 := by
    have h51 : x = ((1 - a) / 2) ^ 2 := by
      linarith [h5]
    nlinarith [h51, h15]

  -- Simplify the inequality to get a quadratic.
  have h17 : a ^ 2 - 6 * a - 7 ≥ 0 := by
    nlinarith [h16]

  -- Solve the quadratic inequality, using previous constraint $a \leq 1$.
  have h19 : a ≤ -1 := by
    nlinarith [sq_nonneg (a + 1), h17, h4]

  exact h19