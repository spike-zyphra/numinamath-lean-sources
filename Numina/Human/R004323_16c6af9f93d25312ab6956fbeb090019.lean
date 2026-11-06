import Mathlib

/- 9. Given that $x, y, z$ are all positive numbers, and $(x+y-z)(y+z-x)(z+x-y)>0$. Prove: $x(y+z)^{2}+y(z+x)^{2}+z(x+y)^{2}-\left(x^{3}+y^{3}+z^{3}\right) \leqslant 9 x y z$. -/
theorem inequalities_252956 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (x + y - z) * (y + z - x) * (z + x - y) > 0) :
    x * (y + z)^2 + y * (z + x)^2 + z * (x + y)^2 -
    (x^3 + y^3 + z^3) ≤ 9 * x * y * z := by
  -- Prove that x + y > z
  have h1 : x + y > z := by
    -- First show that x + y - z > 0
    have h2 : x + y - z > 0 := by
      -- Proof by contradiction
      by_contra h2
      push_neg at h2
      -- If x + y - z ≤ 0, then the product (x+y-z)(y+z-x)(z+x-y) would be non-positive
      -- which contradicts our hypothesis h
      have : (x + y - z) * (y + z - x) * (z + x - y) ≤ 0 := by nlinarith [mul_pos (show 0 < y + z - x from by nlinarith) (show 0 < z + x - y from by nlinarith), h2]
      linarith
    linarith
  -- Prove that y + z > x
  have h2 : y + z > x := by
    -- First show that y + z - x > 0
    have h3 : y + z - x > 0 := by
      -- Proof by contradiction
      by_contra h3
      push_neg at h3
      -- If y + z - x ≤ 0, then the product (x+y-z)(y+z-x)(z+x-y) would be non-positive
      -- which contradicts our hypothesis h
      have : (x + y - z) * (y + z - x) * (z + x - y) ≤ 0 := by nlinarith [mul_pos (show 0 < x + y - z from by nlinarith) (show 0 < z + x - y from by nlinarith), h3]
      linarith
    linarith
  -- Prove that z + x > y
  have h3 : z + x > y := by
    -- First show that z + x - y > 0
    have h4 : z + x - y > 0 := by
      -- Proof by contradiction
      by_contra h4
      push_neg at h4
      -- If z + x - y ≤ 0, then the product (x+y-z)(y+z-x)(z+x-y) would be non-positive
      -- which contradicts our hypothesis h
      have : (x + y - z) * (y + z - x) * (z + x - y) ≤ 0 := by nlinarith [mul_pos (show 0 < x + y - z from by nlinarith) (show 0 < y + z - x from by nlinarith), h4]
      linarith
    linarith
  -- Use nonlinear arithmetic to prove the main inequality
  -- We provide several useful facts about squares being non-negative
  -- and the triangle inequality conditions we just proved (h1, h2, h3)
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
    sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
    mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, h1, h2, h3]
