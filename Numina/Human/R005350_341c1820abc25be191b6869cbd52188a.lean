import Mathlib

/- If $\alpha$ is a real root of the equation $x^{5}-x^{3}+x-2=0$, prove that $\left[\alpha^{6}\right]=3$. (For any real number $a$, we denote by $[a]$ the greatest integer not exceeding $a$.) -/
theorem algebra_607811 {x : ℝ} (h : x^5 - x^3 + x - 2 = 0) : ⌊x^6⌋ = 3 := by 
    -- first establish that x ≥ 0
  have hx: x ≥ 0 := by
    by_contra h'   -- assume for contradiction that x < 0
    rw [not_le] at h'
    have : x^5-x^3+x-2 ≤ -2 := by nlinarith [sq_nonneg (x^2-1), sq_nonneg (x^2-2), pow_two_nonneg (x^3-1)]
    linarith  

  -- Then show x^6 ≥ 3
  have h1: x^6 ≥ (3 : ℝ) := by nlinarith [sq_nonneg (x^2-1), sq_nonneg (x^2-2), pow_two_nonneg (x^3-1)]

  --Finally show x^6 < 4.
  have h2: x^6 < (4 : ℝ) := by nlinarith [sq_nonneg (x^2-1), sq_nonneg (x^2-2), pow_two_nonneg (x^3-1)]

  -- combine the results to conclude floor(x^6) = 3
  apply Int.floor_eq_iff.mpr 
  norm_cast
  