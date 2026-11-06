import Mathlib

open Real

/- Let $x, y>0$ such that $x+y=8$. Show that $\left(x+\frac{1}{y}\right)^{2}+\left(y+\frac{1}{x}\right)^{2} \geq \frac{289}{8}$ -/
theorem inequalities_147302 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 8) :
    (x + 1 / y) ^ 2 + (y + 1 / x) ^ 2 ≥ 289 / 8 := by
  -- First, we apply the Cauchy-Schwarz inequality: (a² + b²) ≥ (a + b)²/2
  have h1 : (x + 1 / y) ^ 2 + (y + 1 / x) ^ 2 ≥ (x + 1 / y + y + 1 / x) ^ 2 / 2 := by
    -- We use the fact that any squared real number is non-negative
    have h : (x + 1 / y - (y + 1 / x)) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith
  -- Next, we show that (x + 1/y + y + 1/x)²/2 ≥ 289/8
  have h2 : (x + 1 / y + y + 1 / x) ^ 2 / 2 ≥ 289 / 8 := by
    -- We prove that x + 1/y + y + 1/x ≥ 17/2
    have h3 : x + 1 / y + y + 1 / x ≥ 17 / 2 := by
      -- Using our constraint that x + y = 8
      have h4 : x + y = 8 := hxy
      -- We prove that 1/x + 1/y ≥ 1/2
      have h5 : 1 / x + 1 / y ≥ 1 / 2 := by
        -- First, we show that x*y ≤ 16 using AM-GM inequality
        have h6 : x * y ≤ 16 := by
          nlinarith [sq_nonneg (x - y), hxy]
        -- Express 1/x + 1/y in terms of x, y, and their product
        have h7 : 1 / x + 1 / y = (x + y) / (x * y) := by
          field_simp [ne_of_gt hx, ne_of_gt hy]
          ring
        -- Substitute x + y = 8
        rw [h7, h4]
        -- Show that 8/(x*y) ≥ 1/2, which is equivalent to x*y ≤ 16
        have h8 : (8 : ℝ) / (x * y) ≥ 1 / 2 := by
          have h9 : 0 < x * y := mul_pos hx hy
          apply (le_div_iff₀ (by linarith)).mpr
          nlinarith
        linarith
      -- Combine x + y = 8 and 1/x + 1/y ≥ 1/2 to get x + 1/y + y + 1/x ≥ 17/2
      nlinarith [h4, h5]
    -- Since (x + 1/y + y + 1/x) ≥ 17/2, we have (x + 1/y + y + 1/x)²/2 ≥ (17/2)²/2 = 289/8
    nlinarith [sq_nonneg (x + 1 / y + y + 1 / x - 17 / 2)]
  -- Combine the two inequalities to complete the proof
  linarith [h1, h2]
