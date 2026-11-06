import Mathlib

/- Prove that all real numbers $x \ne -1$, $y \ne -1$ with $xy = 1$ satisfy the following inequality: 

$$\left(\frac{2+x}{1+x}\right)^2 + \left(\frac{2+y}{1+y}\right)^2 \ge \frac92$$

(Karl Czakler) -/
theorem inequalities_82582 (x y : ℝ) (hx : x ≠ -1) (hy : y ≠ -1) (hxy : x * y = 1) :
    ((2 + x) / (1 + x)) ^ 2 + ((2 + y) / (1 + y)) ^ 2 ≥ 9 / 2 := by
  have h1 : (1 + x) ≠ 0 := by intro; apply hx; linarith
  have h2 : (1 + y) ≠ 0 := by intro; apply hy; linarith
  field_simp [h1, h2]
  rw [le_div_iff (by positivity), ← sub_nonneg]
  ring_nf
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), hxy]