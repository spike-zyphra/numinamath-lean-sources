import Mathlib


/- 4. Let $x$ and $y$ be positive numbers whose sum is 2. Find the maximum value of the expression $x^{2} y^{2}\left(x^{2}+y^{2}\right)$. -/
theorem algebra_290555 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hsum : x + y = 2) :
    x^2 * y^2 * (x^2 + y^2) ≤ 2 ∧ (∃ x' y':ℝ, 0<x' ∧ 0<y' ∧ x'^2*y'^2 * (x'^2 + y'^2) = 2) := by
    -- let's first show that 2 is an obtainable bound (trivial: use 1, 1)
    constructor; rotate_left; use 1, 1; norm_num

    -- let's first show that (x+y)^4-8xy(x^2+y^2) ≥ 0
    have h0:0 ≤ (x + y)^4 - 8 * x * y * (x^2 + y^2) := by
      conv_rhs =>
        calc (x + y)^4 - 8 * x * y * (x^2 + y^2)
        _ = ((x - y)^2) ^ 2 := by ring_nf
      exact sq_nonneg ((x - y) ^ 2)
    -- it follows that 8xy(x^2+y^2) ≤ (x+y)^4
    have h1: 8 * x * y * (x^2 + y^2) ≤ (x + y)^4 := by linarith
    -- we similarly show that 4xy ≤ (x+y)^2
    have h2: 0 ≤ (x + y)^2 - 4 * x * y := by
      conv_rhs =>
        calc (x + y)^2 - 4 * x * y
        _ = (x - y)^2 := by ring_nf
      exact sq_nonneg (x-y)
    have h3: 4 * x * y ≤ (x + y)^2 := by linarith
    -- now we multiply h1 and h3
    have h4: 4 * x * y * (8 * x * y * (x^2 + y^2)) ≤ (x + y)^2 * (x + y)^4 := by
      apply mul_le_mul
      assumption
      assumption
      rotate_left
      exact sq_nonneg (x + y)
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      norm_num
      linarith
      linarith
      apply add_nonneg
      exact sq_nonneg x
      exact sq_nonneg y
    -- simplify both sides
    conv_lhs at h4 =>
      calc 4 * x * y * (8 * x * y * (x ^ 2 + y ^ 2))
      _ = 32 * x^2 * y^2 * (x^2 + y^2) := by ring_nf
    conv_rhs at h4 =>
      calc (x + y)^2 * (x + y)^4
      _ = (x+y)^6 := by ring_nf
    -- we can replace x+y with 2 and simplify
    rw [hsum] at h4; norm_num at h4
    have h5: x^2 * y^2 * (x^2 + y^2) ≤ 2 := by linarith
    assumption