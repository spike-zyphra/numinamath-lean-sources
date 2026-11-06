import Mathlib

/- Simplify the radical $\sqrt{2940}$. -/
theorem algebra_20300 : Real.sqrt 2940 = 14 * Real.sqrt 15 := by
  -- obviously, 2940 is divisible by 10, so 2940 = 2x5x294.
  --  and for 294, we find it is 300-6 = 6x(50-1)=6x7^2
  -- so following holds.
  have h1: (2940:ℝ) = 2*5*6*7^2 := by norm_num
  -- and for 2x5x6, we can extract 2^2.
  have h2: (2940:ℝ) = (14)^2*15 := by
    rw [h1]; norm_num
  have h3: √((14)^2*15) = √(14^2)*√15 := by
    have: 0 ≤ (15:ℝ) := by norm_num
    exact Real.sqrt_mul' (14 ^ 2) this
  -- so √2940 = 14√15
  rw [h2, h3]; simp