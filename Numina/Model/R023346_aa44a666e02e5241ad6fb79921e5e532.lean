import Mathlib

theorem algebra_207146 {x : ℝ} (h : x^3 - 3 * Real.sqrt 2 * x^2 + 6 * x - 2 * Real.sqrt 2 - 8 = 0) :
    x^5 - 41 * x^2 + 2012 = 1998 := by
  have h1 : Real.sqrt 2 > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h2 : x^3 - 3 * Real.sqrt 2 * x^2 + 6 * x - 2 * Real.sqrt 2 = 8 := by 
    linarith
  -- We can rewrite the polynomial as $(x - \sqrt{2})^3 = 8$.
  have h3 : x^3 - 3 * Real.sqrt 2 * x^2 + 6 * x - 2 * Real.sqrt 2 = (x - Real.sqrt 2) ^3 := by 
    ring_nf
    have h11 : Real.sqrt 2 ^2 = 2 := Real.sq_sqrt (by linarith)
    have h12 : Real.sqrt 2 ^3 = Real.sqrt 2 * 2 := by 
      calc
        Real.sqrt 2 ^3 = Real.sqrt 2 * (Real.sqrt 2 ^2) := by ring
        _ = Real.sqrt 2 * 2 := by rw [h11]
    simp [h11, h12]
    <;> nlinarith [Real.sqrt_nonneg 2]
  -- We now solve for x.
  have h4 : (x - Real.sqrt 2) ^3 = 8 := by 
    linarith [h2, h3]
  -- Take the cube root on both sides. Since we are working with real numbers, 
  -- the equation $Y^3 =8$ has a unique real solution $Y=2$.
  have h5 : x - Real.sqrt 2 = 2 := by 
    have h6 : (x - Real.sqrt 2) ^3 - 8 = 0 := by linarith
    have h7 : (x - Real.sqrt 2 - 2) * ((x - Real.sqrt 2) ^2 + 2 * (x - Real.sqrt 2) + 4) = 0 := by
      ring_nf at h6 ⊢
      <;> nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · 
      linarith
    · 
      have h10 : ((x - Real.sqrt 2) ^2 + 2 * (x - Real.sqrt 2) + 4) = 0 := by linarith
      nlinarith [sq_nonneg ((x - Real.sqrt 2) + 1)]
  -- We have proven that $x = 2 + \sqrt{2}$.
  have h6 : x = 2 + Real.sqrt 2 := by linarith
  rw [h6]
  have h81 : Real.sqrt 2 ^2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith)
  -- Compute powers of $2 + \sqrt{2}$.
  have h22 : (2 + Real.sqrt 2) ^2 = 6 + 4 * Real.sqrt 2 := by 
    nlinarith [h81]
  -- Compute $x^5$.
  have h23 : (2 + Real.sqrt 2) ^3 = 20 + 14 * Real.sqrt 2 := by 
    nlinarith [h22, h81]
  -- Compute $x^4$.
  have h24 : (2 + Real.sqrt 2) ^4 = 68 + 48 * Real.sqrt 2 := by 
    nlinarith [h23, h81]
  -- Compute $x^5$.
  have h25 : (2 + Real.sqrt 2) ^5 = 232 + 164 * Real.sqrt 2 := by 
    nlinarith [h24, h81]
  -- Compute the polynomial value.
  nlinarith [h25, h22]