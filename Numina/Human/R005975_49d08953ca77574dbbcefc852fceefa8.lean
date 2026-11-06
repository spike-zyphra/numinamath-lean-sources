import Mathlib
/- Let $x=2001^{1002}-2001^{-1002}$ and $y=2001^{1002}+2001^{-1002}$. Find $x^{2}-y^{2}$. -/
theorem algebra_610946 (x y : ℝ) (hx : x = 2001 ^ (1002 : ℝ) - 2001 ^ (-1002 : ℝ)) (hy : y = 2001 ^ (1002 : ℝ) + 2001 ^ (-1002 : ℝ)) : x ^ 2 - y ^ 2 = -4:= by

  -- Let a = 2001^1002 for easier manipulation
  set a:= (2001 : ℝ) ^ (1002 : ℝ) with ha

  -- Let b = 2001^(-1002) for easier manipulation
  set b:= (2001 : ℝ) ^ (-1002 : ℝ) with hb

  -- Prove that a * b = 1 using properties of exponents
  have hab : a * b = 1:= by
    rw [show (1 : ℝ) = 2001 ^ ((1002 : ℝ) + (-1002 : ℝ)) by ring_nf]
    rw [ha, hb]
    refine Eq.symm (Real.rpow_add (by linarith) 1002 (-1002))

  -- Clear auxiliary definitions to prepare for final calculation
  clear_value a b

  -- Substitute the original expressions for x and y
  subst x y

  -- Complete the proof using linear arithmetic
  linarith
